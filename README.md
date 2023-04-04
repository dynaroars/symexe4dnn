# symexe4dnn

## How to run
navigate to ```./src``` directory, and run the following:
```
python se.py <input>
```
Currently, we have a couple hardcoded input under ```./example```.

## examples
-   
    ```
    python se.py ../example/toy/4x3_1.py
    ```
    This is a toy DNN example that has 4 inputs, 3hidden layers, and 4 neurons at each layer (12 ReLU neurons). SE is able to scale on these kind of small networks.
- 
    ```
    python se.py ../example/acasxu/acasxu_1.py
    ```
    This is a DNN taken from the ACASXU flight navigation benchmark. This network has 5 in/outputs and 6 hidden layers each with 50 ReLU neurons (300 ReLu neurons). We are able to generate the symbolic state of this network, but the symbolic state is too large for the solver(z3) to solve.


## dependencies
- z3-solver

If you want to try the larger example, you will need the following packages 
- onnx
- onnx2pytorch
- torch

A conda envs is provided: ```envs.yaml```
