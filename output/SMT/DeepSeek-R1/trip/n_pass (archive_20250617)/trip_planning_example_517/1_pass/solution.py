from z3 import *

def main():
    s = Solver()
    city_dict = {
        'Bucharest': 0,
        'Warsaw': 1,
        'Stuttgart': 2,
        'Copenhagen': 3,
        'Dubrovnik': 4
    }
    num_days = 19
    c = [Int('c_%d' % i) for i in range(1, 21)]
    travel = [Bool('travel_%d' % i) for i in range(1, 20)]
    
    for i in range(20):
        s.add(c[i] >= 0)
        s.add(c[i] <= 4)
    
    allowed_edges = [
        (1, 3), (3, 1),
        (2, 3), (3, 2),
        (1, 2), (2, 1),
        (0, 3), (3, 0),
        (0, 1), (1, 0),
        (3, 4), (4, 3)
    ]
    
    for i in range(19):
        s.add(If(travel[i], c[i] != c[i+1], c[i] == c[i+1]))
        edge_constraints = []
        for a, b in allowed_edges:
            edge_constraints.append(And(c[i] == a, c[i+1] == b))
        s.add(Implies(travel[i], Or(edge_constraints)))
    
    s.add(Sum([If(travel[i], 1, 0) for i in range(19)]) == 4)
    
    required_days = [6, 2, 7, 3, 5]
    for city in range(5):
        total_days = 0
        for i in range(19):
            total_days += If(c[i] == city, 1, 0)
        for i in range(19):
            total_days += If(And(travel[i], c[i+1] == city), 1, 0)
        s.add(total_days == required_days[city])
    
    s.add(Or(c[6] == 2, And(travel[6], c[7] == 2)))
    s.add(Or(c[12] == 2, And(travel[12], c[13] == 2)))
    
    wedding_days = []
    for i in range(6):
        wedding_days.append(Or(c[i] == 0, And(travel[i], c[i+1] == 0)))
    s.add(Or(wedding_days))
    
    if s.check() == sat:
        m = s.model()
        city_names = {
            0: 'Bucharest',
            1: 'Warsaw',
            2: 'Stuttgart',
            3: 'Copenhagen',
            4: 'Dubrovnik'
        }
        for day in range(1, 20):
            idx = day - 1
            if m.eval(travel[idx]):
                start_city = m.eval(c[idx])
                end_city = m.eval(c[idx+1])
                start_name = city_names[start_city.as_long()]
                end_name = city_names[end_city.as_long()]
                print(f"Day {day}: {start_name} and {end_name}")
            else:
                city_val = m.eval(c[idx])
                city_name = city_names[city_val.as_long()]
                print(f"Day {day}: {city_name}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()