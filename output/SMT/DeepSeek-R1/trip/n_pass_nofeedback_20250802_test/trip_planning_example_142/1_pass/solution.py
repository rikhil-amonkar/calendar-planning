import json
from z3 import *

def main():
    # Define the city constants
    MADRID = 0
    DUBLIN = 1
    TALLINN = 2
    city_names = {MADRID: "Madrid", DUBLIN: "Dublin", TALLINN: "Tallinn"}
    
    # Create the solver
    s = Solver()
    
    # Define variables
    start_city = Int('start_city')
    end_city = [Int(f'end_city_{i}') for i in range(7)]  # for days 1 to 7
    
    # Domain constraints for start_city and end_city
    s.add(start_city >= 0, start_city <= 2)
    for i in range(7):
        s.add(end_city[i] >= 0, end_city[i] <= 2)
    
    # Lists to hold the Madrid, Dublin, Tallinn indicators for each day
    M_list = []
    D_list = []
    T_list = []
    
    # Day 1 (index0)
    start = start_city
    end0 = end_city[0]
    M0 = Or(start == MADRID, end0 == MADRID)
    D0 = Or(start == DUBLIN, end0 == DUBLIN)
    T0 = Or(start == TALLINN, end0 == TALLINN)
    M_list.append(M0)
    D_list.append(D0)
    T_list.append(T0)
    # Travel constraint for day1: if start != end0, then must be a direct flight
    s.add(If(start != end0,
             Or(
                 And(start == MADRID, end0 == DUBLIN),
                 And(start == DUBLIN, end0 == MADRID),
                 And(start == DUBLIN, end0 == TALLINN),
                 And(start == TALLINN, end0 == DUBLIN)
             ),
             True  # if not traveling, no constraint
          ))
    
    # Days 2 to 7 (indices 1 to 6)
    for i in range(1, 7):
        prev_end = end_city[i-1]
        curr_end = end_city[i]
        M_i = Or(prev_end == MADRID, curr_end == MADRID)
        D_i = Or(prev_end == DUBLIN, curr_end == DUBLIN)
        T_i = Or(prev_end == TALLINN, curr_end == TALLINN)
        M_list.append(M_i)
        D_list.append(D_i)
        T_list.append(T_i)
        # Travel constraint: if the end city changes, must be a direct flight
        s.add(If(prev_end != curr_end,
                 Or(
                     And(prev_end == MADRID, curr_end == DUBLIN),
                     And(prev_end == DUBLIN, curr_end == MADRID),
                     And(prev_end == DUBLIN, curr_end == TALLINN),
                     And(prev_end == TALLINN, curr_end == DUBLIN)
                 ),
                 True
             ))
    
    # Total counts
    total_M = Sum([If(m, 1, 0) for m in M_list])
    total_D = Sum([If(d, 1, 0) for d in D_list])
    total_T = Sum([If(t, 1, 0) for t in T_list])
    s.add(total_M == 4)
    s.add(total_D == 3)
    s.add(total_T == 2)
    
    # Must be in Tallinn on day6 and day7 (which are at indices 5 and 6 in T_list)
    s.add(T_list[5] == True)  # day6
    s.add(T_list[6] == True)  # day7
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(7):
            if day == 0:
                start_val = model.eval(start_city).as_long()
                end_val = model.eval(end_city[0]).as_long()
                cities_set = {start_val, end_val}
            else:
                start_val = model.eval(end_city[day-1]).as_long()
                end_val = model.eval(end_city[day]).as_long()
                cities_set = {start_val, end_val}
            # Convert set to sorted list of city names
            cities_list = sorted([city_names[x] for x in cities_set])
            itinerary.append({"day": day+1, "place": cities_list})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()