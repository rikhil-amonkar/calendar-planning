from z3 import *

def main():
    # Mapping cities to integers
    city_names = ['Stuttgart', 'Bucharest', 'Geneva', 'Valencia', 'Munich']
    days_arr = [2, 2, 4, 6, 7]  # Corresponding days for each city
    flight_pairs = [(2, 4), (4, 3), (1, 3), (4, 1), (3, 0), (2, 3)]  # Direct flight pairs (as integers)
    
    # Create allowed_set with both (i,j) and (j,i)
    allowed_set = set()
    for (i, j) in flight_pairs:
        allowed_set.add((i, j))
        allowed_set.add((j, i))
    allowed_list = list(allowed_set)
    
    # Declare variables for the sequence
    s0, s1, s2, s3, s4 = Ints('s0 s1 s2 s3 s4')
    s = [s0, s1, s2, s3, s4]
    solver = Solver()
    
    # Each s_i is between 0 and 4 and all are distinct
    for i in range(5):
        solver.add(s[i] >= 0, s[i] <= 4)
    solver.add(Distinct(s0, s1, s2, s3, s4))
    
    # Flight constraints for consecutive cities
    for k in range(4):
        sk = s[k]
        sk1 = s[k+1]
        or_conditions = []
        for pair in allowed_list:
            or_conditions.append(And(sk == pair[0], sk1 == pair[1]))
        solver.add(Or(or_conditions))
    
    # Position variables for Geneva (index2) and Munich (index4)
    pos_g = Int('pos_g')
    pos_m = Int('pos_m')
    solver.add(pos_g >= 0, pos_g <= 4)
    solver.add(pos_m >= 0, pos_m <= 4)
    
    # Define pos_g: the position of Geneva (city2) in the sequence
    solver.add(Or(
        And(s0 == 2, pos_g == 0),
        And(s1 == 2, pos_g == 1),
        And(s2 == 2, pos_g == 2),
        And(s3 == 2, pos_g == 3),
        And(s4 == 2, pos_g == 4)
    ))
    
    # Define pos_m: the position of Munich (city4) in the sequence
    solver.add(Or(
        And(s0 == 4, pos_m == 0),
        And(s1 == 4, pos_m == 1),
        And(s2 == 4, pos_m == 2),
        And(s3 == 4, pos_m == 3),
        And(s4 == 4, pos_m == 4)
    ))
    
    # Function to compute arrival day for a city
    def compute_arrival(s_list, pos_c, days_arr):
        total = 0
        for j in range(5):
            term = If(j < pos_c,
                    If(s_list[j] == 0, days_arr[0],
                    If(s_list[j] == 1, days_arr[1],
                    If(s_list[j] == 2, days_arr[2],
                    If(s_list[j] == 3, days_arr[3],
                    If(s_list[j] == 4, days_arr[4], 0)))),
                    0)
            total = total + term
        return 1 + total - pos_c
    
    a_g = compute_arrival(s, pos_g, days_arr)
    a_m = compute_arrival(s, pos_m, days_arr)
    solver.add(a_g <= 4)  # Geneva constraint
    solver.add(a_m <= 10) # Munich constraint
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        seq_val = [model.evaluate(s[i]).as_long() for i in range(5)]
        
        # Compute arrival days for each city in the sequence
        a = [0] * 5
        a[0] = 1
        for i in range(1, 5):
            prev_city = seq_val[i-1]
            a[i] = a[i-1] + (days_arr[prev_city] - 1)
        
        # Build itinerary for each day (1 to 17)
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
                city_str = cities_today
            itinerary.append({"day": day, "city": city_str})
        
        # Output as JSON
        import json
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()