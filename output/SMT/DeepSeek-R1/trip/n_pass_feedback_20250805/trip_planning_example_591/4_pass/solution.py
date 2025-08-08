from z3 import *

def main():
    city_names = ['Stuttgart', 'Bucharest', 'Geneva', 'Valencia', 'Munich']
    days_arr = [2, 2, 4, 6, 7]
    flight_pairs = [(2, 4), (4, 3), (1, 3), (4, 1), (3, 0), (2, 3)]
    
    allowed_set = set()
    for (i, j) in flight_pairs:
        allowed_set.add((i, j))
        allowed_set.add((j, i))
    allowed_list = list(allowed_set)
    
    s0, s1, s2, s3, s4 = Ints('s0 s1 s2 s3 s4')
    s = [s0, s1, s2, s3, s4]
    solver = Solver()
    
    for i in range(5):
        solver.add(s[i] >= 0, s[i] <= 4)
    solver.add(Distinct(s0, s1, s2, s3, s4))
    
    for k in range(4):
        sk = s[k]
        sk1 = s[k+1]
        or_conditions = []
        for pair in allowed_list:
            or_conditions.append(And(sk == pair[0], sk1 == pair[1]))
        solver.add(Or(or_conditions))
    
    pos_g = Int('pos_g')
    pos_m = Int('pos_m')
    solver.add(pos_g >= 0, pos_g <= 4)
    solver.add(pos_m >= 0, pos_m <= 4)
    
    for i in range(5):
        solver.add(Implies(s[i] == 2, pos_g == i))
        solver.add(Implies(s[i] == 4, pos_m == i))
    
    def compute_arrival(s_list, pos_c, days_arr):
        total = 0
        for j in range(5):
            inner = 0
            for idx in range(5):
                inner = If(s_list[j] == idx, days_arr[idx], inner)
            term = If(j < pos_c, inner, 0)
            total = total + term
        return 1 + total - pos_c
    
    a_g = compute_arrival(s, pos_g, days_arr)
    a_m = compute_arrival(s, pos_m, days_arr)
    solver.add(a_g <= 4, a_g >= 1)
    solver.add(a_m <= 10, a_m >= 4)
    
    if solver.check() == sat:
        model = solver.model()
        seq_val = [model.evaluate(s[i]).as_long() for i in range(5)]
        a = [0] * 5
        a[0] = 1
        for i in range(1, 5):
            prev_city = seq_val[i-1]
            a[i] = a[i-1] + days_arr[prev_city] - 1
        
        itinerary = []
        for day in range(1, 18):
            cities_today = []
            for i in range(5):
                city_index = seq_val[i]
                start_day = a[i]
                end_day = start_day + days_arr[city_index] - 1
                if start_day <= day <= end_day:
                    cities_today.append(city_names[city_index])
            if len(cities_today) == 1:
                city_str = cities_today[0]
            else:
                city_str = ', '.join(cities_today)
            itinerary.append({"day": day, "city": city_str})
        
        import json
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()