cond_workshop = Or([
    (stay[d-1] == 2) | (fly[d-1] & (stay[d] == 2)) 
    for d in range(3, 10)
])