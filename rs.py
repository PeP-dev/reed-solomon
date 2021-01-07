class ReedSolomon:   
    # On travaille dans un corps de Galois de valeur 2^8 = 256
    gfSize = 256 
    # http://icaiit.org/proceedings/2nd_ICAIIT/7.pdf
    # Le polynome générateur de la forme x^8 + x^4 + x^3 + x^2 + 1 = 100011101
    genPoly = 285 
    log = [0]*gfSize
    antilog = [0]*gfSize

    def _galPolynomialAddition(self, a, b):
        polSum = [0] * max(len(a), len(b))
        for index in range(0, len(a)):
            polSum[index + len(polSum) - len(a)] = a[index]
        for index in range(0, len(b)):
            polSum[index + len(polSum) - len(b)] ^= b[index]
        return (polSum)

    def _genLogAntilogArrays(self):
        self.antilog[0] = 1
        self.log[0] = 0
        self.antilog[255] = 1
        #On multiplie par 2 (équivalent à déplacer tout les bits d'une position vers la gauche, et plus parlant comme on utilise un code cyclique)
        for i in range(1,255):
            self.antilog[i] = self.antilog[i-1] << 1 
            if self.antilog[i] >= self.gfSize:
                self.antilog[i] = self.antilog[i] ^ self.genPoly
            self.log[self.antilog[i]] = i

    def _galMult(self,x,y):
        if ((x == 0) or (y == 0)):
            val = 0
        else:
            val = self.antilog[(self.log[x] + self.log[y])%255]
        return val

    def _galDiv(self, x, y):
        val = 0
        if (y == 0):
            raise ZeroDivisionError()
        if (x == 0):
            val = 0
        else:
            val = self.antilog[(self.log[x] - self.log[y] + 255)%255]
        return val

    def _galPow(self,x, p):
        if x == 0:
            return 0
        return self.antilog[(self.log[x] * p) % 255]

    def _galMultiplicationPolynomiale(self, x,y):
        result = [0]*(len(x)+len(y)-1)
        for i in range(len(x)):
            for j in range(len(y)):
                result[i+j] ^= self._galMult(x[i],y[j])
        return result

    def _galDvtPolynome(self,nbErrorBits):
        # On commence à multiplier à la valeur 1
        result = [1]
        # On multiplie autant de racines que de bits nécessaires pour trouver les erreurs => (x + 1)*(x + 2)*(x + 4)*....*(x +a**nbErrorBits)
        for index in range(nbErrorBits):
            # Racine du polynome (x + a**index)
            root = [1, self.antilog[index]]
            result = self._galMultiplicationPolynomiale(result, root)
        return result

    def __init__(self):
        self._genLogAntilogArrays()

    def _trimArray(self,arr):
        if len(arr)>0:
            while(len(arr)>0 and arr[0]==0): arr.pop(0)

    def _galPolynomialDivision(self,dividend, divisor):
        sor = divisor.copy()
        end = dividend.copy()
        self._trimArray(end)
        self._trimArray(sor)
        normalizer = sor[0]
        if(len(end)==1 or len(sor)==1):
            end.append(0)
            sor.append(0)
        out = end.copy()
        for i in range(len(end)-(len(sor)-1)):
            out[i] =self._galDiv(out[i],normalizer)
            coef = out[i]
            if coef != 0: 
                for j in range(1, len(sor)): 
                    out[i + j] ^= self._galMult(sor[j], coef)
        separator = -(len(sor)-1)
        return out[:separator], out[separator:]

    def _galEvaluatePolynomial(self,encoded,alpha):
        return self._galPolynomialDivision(encoded,[1,alpha])[1][0]

    def _galGenerateSyndrome(self,encoded,nbErrorBits):
        polynomial = []
        for i in range(nbErrorBits):
            polynomial.insert(0,self._galEvaluatePolynomial(encoded,self.antilog[i]))
        return polynomial

    def _degree(self,arr):
        for i in range(len(arr)):
            if arr[i] != 0:
                return len(arr)-i-1
        return 0

    def _galEuclideanAlgorithm(self,a,b,minDeg):
        r0 = a.copy()
        r1 = b.copy()

        u0 = [1]
        u1 = [0]

        v0 = [0]
        v1 = [1]
        while True:
            q,r = self._galPolynomialDivision(r0,r1)
            u1,u0 = self._galPolynomialAddition(u0,self._galMultiplicationPolynomiale(q,u1)),u1
            v1,v0 = self._galPolynomialAddition(v0,self._galMultiplicationPolynomiale(q,v1)),v1
            r0,r1 = r1,r
            if(self._degree(r1)<=minDeg):
                return r1,u1,v1

    def encode(self,message,nbErrorBits):
        polynomial = self._galDvtPolynome(nbErrorBits)
        charCodes = list(map(ord,message))+[0]*nbErrorBits
        charCodes[-nbErrorBits:] = self._galPolynomialDivision(charCodes,polynomial)[1]
        return charCodes

    def horner(self,polynomial,x):
        result = 0
        deriv = 0
        for a in polynomial:
            deriv = self._galMult(x,deriv)^result
            result = self._galMult(x,result)^a
        return result,deriv
    
    def _galChienSearch(self,locator,msgLen):
        
        alpha = self._galDiv(1,self.antilog[self.gfSize - msgLen])

        chien_array = [0] * len(locator)
        for i in range(len(locator)):
            chien_array[i] = self._galMult(locator[i], self._galPow(alpha, i))
        roots = []
        for i in range(msgLen):
            res = functools.reduce(lambda x,y: x^y, chien_array)
            for j in range(1, len(chien_array)):
                index = len(chien_array) - j - 1
                chien_array[index] = self._galMult(chien_array[index], self.antilog[j])
            if res == 0:
                roots.append(msgLen - i -1)
        return roots

    def _galCorrectErrors(self,message,errors,locator,evaluator):
        msg = message.copy()
        offset = len(message)-1
        for error in errors:
            evalIndex = self.antilog[error]
            invEval = self._galDiv(1,evalIndex)
            k_inv = self._galDiv(
                self._galEvaluatePolynomial(evaluator,invEval),
                self.horner(locator,invEval)[1]
                )
            errVal =self._galMult(evalIndex,k_inv)
            msg[offset-error] ^=errVal
        return msg

    def decode(self,message,nbErrorBits):
        syndrome = self._galGenerateSyndrome(message,nbErrorBits)
        hasError = False
        for val in syndrome:
            if val > 0:
                hasError = True
        if not hasError:
            return message[:-nbErrorBits]
        x = [1]+[0]*nbErrorBits
        evaluator,_,locator = self._galEuclideanAlgorithm(x,syndrome,nbErrorBits/2)
        self._trimArray(evaluator)
        self._trimArray(locator)
        print(evaluator,locator)
        errors = self._galChienSearch(locator,len(message))
        if(len(errors)==0):
            print(nbErrorBits/2,'erreurs ou plus, décodage impossible')
            return None
        print("Erreurs detéctées aux positions :",errors)

        return self._galCorrectErrors(message,errors,locator,evaluator)

import functools 
rs = ReedSolomon()
maxErreurs = 8
message = "abcdedfdfd !"
encoded = rs.encode(message,maxErreurs*2)
correct = encoded.copy()
encoded[1]=125
encoded[2]=100
encoded[0]=99

print(functools.reduce(lambda x,y: x+chr(y),encoded,""))
print("Encoded with error:",encoded)
decoded = rs.decode(encoded,maxErreurs*2)
print("Message corrigé : ", decoded)
print("Reussi ? :", correct == decoded)
print(functools.reduce(lambda x,y: x+chr(y),decoded,""))

print('---------------------')