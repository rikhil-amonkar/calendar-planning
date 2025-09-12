conditions = [
    (cond0, true0),
    (cond1, true1),
    (cond2, true2),
    (cond3, true3),
    (cond4, true4),
]

for condition, action in conditions:
    if condition:
        action
        break
else:
    default