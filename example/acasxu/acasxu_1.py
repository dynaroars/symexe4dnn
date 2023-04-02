import onnx
import onnx2pytorch
import torch
import pathlib



def get_acasxu_dummy(fidx):
    floc = pathlib.Path(__file__).parent.resolve()

    fname = floc / [".net/ACASXU_1.onnx", ".net/ACASXU_1.onnx", ".net/ACASXU_2.onnx", ".net/ACASXU_3.onnx", ][fidx]
    onnx_model = onnx.load(fname)
    torch_model = onnx2pytorch.ConvertModel(onnx_model)
    # (weights, bias, use activation function relu or not)
    rand_weights = lambda x: [random.uniform(-1,1) for _ in range(x)]
    rand_bias    = lambda  : random.uniform(-1,1) 

    hidden_layer0 = [(w, b, True) for w,b in zip(torch_model.MatMul_H0.weight.transpose(0,1).tolist(), torch_model.MatMul_H0.bias.tolist())]

    hidden_layer5 = [(w, b, True) for w,b in zip(torch_model.MatMul_H5.weight.transpose(0,1).tolist(), torch_model.MatMul_H5.bias.tolist())]

    hidden_layer4 = [(w, b, True) for w,b in zip(torch_model.MatMul_H4.weight.transpose(0,1).tolist(), torch_model.MatMul_H4.bias.tolist())]

    hidden_layer3 = [(w, b, True) for w,b in zip(torch_model.MatMul_H3.weight.transpose(0,1).tolist(), torch_model.MatMul_H3.bias.tolist())]

    hidden_layer2 = [(w, b, True) for w,b in zip(torch_model.MatMul_H2.weight.transpose(0,1).tolist(), torch_model.MatMul_H2.bias.tolist())]

    hidden_layer1 = [(w, b, True) for w,b in zip(torch_model.MatMul_H1.weight.transpose(0,1).tolist(), torch_model.MatMul_H1.bias.tolist())]

    out_layer     = [(w, b, False) for w,b in zip(torch_model.MatMul_y_out.weight.transpose(0,1).tolist(), torch_model.MatMul_y_out.bias.tolist())]

    this_dnn = [hidden_layer0, hidden_layer1, hidden_layer2, hidden_layer3, hidden_layer4, hidden_layer5, out_layer]

    # return this_dnn, torch_model, onnx_model
    return this_dnn