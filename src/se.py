from z3 import *
from time import perf_counter
def dnn_num_inputs(dnn):
    # returns the number of inputs for a dnn
    return len(dnn[0][0][0])

def neuron_name(layer, neuron, layers = -2):
    # generate neuron name like i0, n01,o1...
    if layer==-1:
        return 'i'+str(neuron)
    elif layer+1==layers:
        return 'o'+str(neuron)
    else:
        return 'n' + str(layer)+ str(neuron)

def create_input(dnn):
    # creates z3/python variable for inputs of a dnn
    for idx in range(dnn_num_inputs(dnn)):
        nName = neuron_name(-1,idx)
        globals()[nName] = Real(nName)

def create_aRefs(dnn):
    # creates z3/python variable for each neurons
    aRefs = {}
    layers = len(dnn)
    for layer in range(layers):
        for neurons in range(len(dnn[layer])):
            nName = neuron_name(layer,neurons,layers=layers)
            globals()[nName] = Real(nName)

def get_weights(neuron):
    # get the weights of a neuron
    return neuron[0]

def weighted_sum(in_1, in_2):
    # weighted sum
    sum = in_1[0]*in_2[0]
    for a,b in list(zip(in_1,in_2))[1:]:
        sum += a*b
    return sum

def get_bias(neuron):
    return neuron[1]

def use_relu(neuron):
    # tells if a neuron use ReLU or not
    return neuron[2]

def symbolic_execution(dnn):

    layers = len(dnn)
    create_aRefs(dnn) #creates neurons
    create_input(dnn)
    symbolic_states = []
    aRefs = globals()

    for layer in range(layers):
        # get inputs from last layer(as a list)
        input_num    = len(get_weights(dnn[layer][0]))
        input_names  = list(map(lambda x: neuron_name(layer-1,x),list(range(input_num))))
        inputs = list(map(lambda x:aRefs[x],input_names))

        #######################################
        print('layer: ' + str(layer))         #
        print('\t inputs: '+str(input_names)) #
        #######################################
        for neuron in range(len(dnn[layer])):
            # generate formula
            nName   = neuron_name(layer,neuron,layers)
            weights = get_weights(dnn[layer][neuron])
            exp = weighted_sum(weights,inputs) + get_bias(dnn[layer][neuron])
                # exp => formula for current neuron(without ReLU)

            if use_relu(dnn[layer][neuron]):
                symbolic_states.append(aRefs[nName] == If(exp<=0,0,exp))
            else:
                symbolic_states.append(aRefs[nName] == exp)
            #######################################
            print('\t\t'+nName + '=' +str(exp))   #
            #######################################

    return And(symbolic_states)

def my_symbolic_execution(dnn):
    # just a wrapper for symbolic_execution()
    ##########################################
    print('\n=========SE started=========')  #
    ##########################################
    start = perf_counter()
    temp = symbolic_execution(dnn)
    ##########################################
    print('============================')    #
    print('DONE:')                           #
    print('symbolic states obtained')        #
    print(str(dnn_num_inputs(dnn))+'\tinputs')
    print(str(len(dnn))+'\tlayers')          #
    print(str(len(dnn[-1]))+'\toutputs')     #
    print('time used: ')                     #
    print(str(perf_counter()-start) + ' s')  #
    print('\n=========SE finished=========') #
    ##########################################
    return temp

def test(name='test'):
    print('\n\n=============RUNNING:==========')
    print('============='+name+'=============')
    def get_dnn():
        # (weights, bias, use activation function relu or not)
        n00 = ([1.0, -1.0], 0.0, True)
        n01 = ([1.0, 1.0], 0.0, True)
        hidden_layer0 = [n00,n01]
        n10 = ([0.5, -0.2], 0.0, True)
        n11 = ([-0.5, 0.1], 0.0, True)
        hidden_layer1 = [n10, n11]
        # don't use relu for outputs
        o0 = ([1.0, -1.0], 0.0, False)
        o1 = ([-1.0, 1.0], 0.0, False)
        output_layer = [o0, o1]
        this_dnn = [hidden_layer0, hidden_layer1, output_layer]
        return this_dnn


    symbolic_states = my_symbolic_execution(get_dnn())

    print("1. Generating random inputs and obtain outputs")
    solve(symbolic_states)

    print("2. Simultation concrete execution")
    g = z3.And([i0 == 1.0, i1 == -1.0])
    solve(z3.And(symbolic_states, z3.And(g)))

    print("3. Checking assertions")
    #1
    g = z3.Implies(z3.And([n00 > 0.0, n01 == 0.0]), o0 > o1)
    print(g)
    prove(z3.Implies(symbolic_states, g))
    #2
    g = z3.Implies(z3.And([i0 - i1 > 0.0, i0 + i1 <= 0.0]), o0 > o1)
    print(g)
    prove(z3.Implies(symbolic_states, g))
    #3
    g = z3.Implies(i0 - i1 > 0.0, o0 > o1)
    print(g)
    prove(z3.Implies(symbolic_states, g))
    print('============='+name+'=============')
    print('=============DONE:============')

def test2(name='test2'):
    print('\n\n=============RUNNING:==========')
    print('============='+name+'=============')
    def get_dnn():
        # (weights, bias, use activation function relu or not)
        n00 = ([1.0, 1.0], 0.1, True)
        n01 = ([0.5, 0.5], 0.2, True)
        n02 = ([1.5, 0.0], 0.3, True)
        n03 = ([0.0, 1.5], 0.4, True)
        hidden_layer0 = [n00,n01,n02,n03]
        n10 = ([0.5, -0.5, 0.0, 1.0], 1.0, True)
        n11 = ([-0.5, 0.1, 2.0, -3.0], -2.0, True)
        n12 = ([0.5, -0.2, 0.4, 1.0], 3.0, True)
        n13 = ([-0.5, 0.1, 1.2, -0.5], -4.0, True)
        hidden_layer1 = [n10, n11,n12,n13]
        n20 = ([0.5, -0.2, 0.5, 0.5], -1.0, True)
        n21 = ([-0.5, 0.1, 1.1, -1.0], 1.0, True)
        n22 = ([0.5, -0.2, -0.5, 0.2], 1.0, True)
        n23 = ([-0.5, 0.1, 1.1, 2.0], -1.0, True)
        hidden_layer2 = [n20,n21,n22,n23]
        # don't use relu for outputs
        o0 = ([0.5, 0.5, -0.4, 1.0], 1.0, False)
        o1 = ([-0.2, -0.5, 1.1, 2.0], 1.0, False)
        output_layer = [o0, o1]
        this_dnn = [hidden_layer0, hidden_layer1, hidden_layer2, output_layer]
        return this_dnn


    symbolic_states = my_symbolic_execution(get_dnn())

    print("1. Generating random inputs and obtain outputs")
    solve(symbolic_states)

    print("2. Simultation concrete execution")
    g = z3.And([i0 == 9, i1 == -10])
    solve(And(symbolic_states, And(g)))

    print("3. Checking assertions")
    #1
    g = Implies(And([i0 > 0.0, i1 > 0.0]), And([o0>0,  o1>0]))
    print(g)
    prove(z3.Implies(symbolic_states, g))
    #2
    g = Implies(And([i0==i1,i0<0]), And([o0!=0, o1!=0]))
    print(g)
    prove(z3.Implies(symbolic_states, g))
    #3
    g = Implies(i0 == i1 , o0 == o1)
    print(g)
    prove(Implies(symbolic_states, g))
    print('============='+name+'=============')
    print('=============DONE:============')

if __name__ == '__main__':
    test()
    test2()
