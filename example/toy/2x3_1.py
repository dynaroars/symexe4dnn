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