from z3 import *
import json

def main():
    I, L, S = 0, 1, 2
    city_dict = {'Istanbul': I, 'London': L, 'Santorini': S}
    inv_city_dict = {I: 'Istanbul', L: 'London', S: 'Santorini'}

    s = [Int(f's_{i}') for i in range(10)]
    e10 = Int('e10')

    solver = Solver()

    for i in range(10):
        solver.add(s[i] >= 0, s[i] <= 2)
    solver.add(e10 >= 0, e10 <= 2)

    for i in range(9):
        solver.add(Or(
            s[i] == s[i+1],
            And(s[i] == I, s[i+1] == L),
            And(s[i] == L, s[i+1] == I),
            And(s[i] == L, s[i+1] == S),
            And(s[i] == S, s[i+1] == L)
        ))
    
    solver.add(Or(
        s[9] == e10,
        And(s[9] == I, e10 == L),
        And(s[9] == L, e10 == I),
        And(s[9] == L, e10 == S),
        And(s[9] == S, e10 == L)
    ))

    def count_days(c):
        total = 0
        for i in range(9):
            total += If(Or(s[i] == c, s[i+1] == c), 1, 0)
        total += If(Or(s[9] == c, e10 == c), 1, 0)
        return total

    london_days = count_days(L)
    santorini_days = count_days(S)
    istanbul_days = count_days(I)

    solver.add(london_days == 3)
    solver.add(santorini_days == 6)
    solver.add(istanbul_days == 3)
    
    solver.add(Or(s[4] == S, s[5] == S))
    solver.add(Or(s[9] == S, e10 == S))

    if solver.check() == sat:
        m = solver.model()
        s_vals = [m.evaluate(s[i]) for i in range(10)]
        e10_val = m.evaluate(e10)
        
        end_cities = []
        for i in range(1, 10):
            end_cities.append(s_vals[i])
        end_cities.append(e10_val)
        
        itinerary_list = []
        for day in range(1, 11):
            city_val = end_cities[day-1]
            city_index = city_val.as_long()
            city_name = inv_city_dict[city_index]
            itinerary_list.append({'day': day, 'place': city_name})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()