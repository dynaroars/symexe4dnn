import z3


class FullyConnectedDNN:
    def __init__(self, layers):
        self.layers = layers
        self.first_hidden_layer = self.layers[0]
        self.hidden_layers = self.layers[:-1]
        self.output_layer = self.layers[-1]

    def eval(self, inp):

        myinp = inp
        for hidden_layer in self.hidden_layers:
            myoutp = self.eval_layer(myinp, hidden_layer, activation=True)
            myinp = myoutp
        myoutp = self.eval_layer(myinp, self.output_layer, activation=False)
        return myoutp

    def eval_layer(self, inp, hidden_layer, activation):
        vs = [self.eval_neuron(inp, weights) for weights in hidden_layer]
        if activation:
            vs = [self.relu(v) for v in vs]
        return vs

    @classmethod
    def create_random(dims):
        pass


class FullyConnectDNN_CONCRETE(FullyConnectedDNN):
    @classmethod
    def relu(cls, v):
        return max(0.0, v)

    @classmethod
    def eval_neuron(cls, vs, ws, b=0.0):
        # print(vs)
        # print(ws)
        return sum(v * w for v, w in zip(vs, ws)) + b


class FullyConnectDNN_SYMBOLIC(FullyConnectedDNN):
    zero = z3.RealVal(0.0)

    @classmethod
    def relu(cls, v):
        return z3.simplify(z3.If(cls.zero >= v, cls.zero, v))

    @classmethod
    def eval_neuron(cls, vs, ws, b=zero):
        return z3.simplify(sum(v * w for v, w in zip(vs, ws)) + b)


# Example a from Property Inference for DNNs paper (Divya Gopinath)

hidden_layer1 = [[1.0, -1.0], [1.0, 1.0]]
hidden_layer2 = [[0.5, -0.2], [-0.5, 0.1]]
hidden_layer3 = [[1.0, -1.0], [-1.0, 1.0]]
dnn = [hidden_layer1, hidden_layer2, hidden_layer3]
FCDNN = FullyConnectDNN_CONCRETE(dnn)

concrete_outp = FCDNN.eval([1.0, -1.0])
print(concrete_outp)


dnn = [hidden_layer1, hidden_layer2, hidden_layer3]
# dnn += dnn  # 4
# dnn += dnn  # 8
# dnn += dnn  # 16
# dnn += dnn  # 32
# dnn += dnn  #  64
# dnn += dnn  # 128
# dnn += dnn  # 256 ..

# dnn = [hidden_layer1, hidden_layer2]
# FCDNN = FullyConnectDNN_SYMBOLIC(dnn)
# symbolic_outp = FCDNN.eval([z3.Real("x"), z3.Real("y")])

# print(symbolic_outp)
# z3.solve(z3.And(*symbolic_outp))
