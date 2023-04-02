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