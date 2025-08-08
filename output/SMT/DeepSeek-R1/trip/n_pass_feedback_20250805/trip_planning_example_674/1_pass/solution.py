from z3 import *
import json

def main():
    # Cities and their indices
    cities = ["Helsinki", "Warsaw", "Madrid", "Split", "Reykjavik", "Budapest"]
    # Durations for each city: [Helsinki, Warsaw, Madrid, Split, Reykjavik, Budapest]
    dur = [2, 3, 4, 4, 2, 4]
    
    # Directed flight edges: (from, to)
    edges = [
        (0,4), (4,0),  # Helsinki <-> Reykjavik
        (5,1), (1,5),  # Budapest <-> Warsaw
        (2,3), (3,2),  # Madrid <-> Split
        (0,3), (3,0),  # Helsinki <-> Split
        (0,2), (2,0),  # Helsinki <-> Madrid
        (0,5), (5,0),  # Helsinki <-> Budapest
        (4,1), (1,4),  # Reykjavik <-> Warsaw
        (0,1), (1,0),  # Helsinki <-> Warsaw
        (2,5), (5,2),  # Madrid <-> Budapest
        (4,5), (5,4),  # Budapest <-> Reykjavik
        (2,1), (1,2),  # Madrid <-> Warsaw
        (1,3), (3,1),  # Warsaw <-> Split
        (4,2)          # Reykjavik -> Madrid
    ]
    
    # Create Z3 variables for the order of cities
    order = [Int(f'order_{i}') for i in range(6)]
    
    s = Solver()
    
    # Each order[i] must be between 0 and 5
    for i in range(6):
        s.add(And(order[i] >= 0, order[i] < 6))
    
    # All elements in order must be distinct
    s.add(Distinct(order))
    
    # Flight constraints: consecutive cities must have a direct flight
    for i in range(5):
        constraints = []
        for (a, b) in edges:
            constraints.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(constraints))
    
    # Build prefix sums: prefix_arr[k] = sum_{i=0}^{k-1} (dur[order[i]] - 1)
    prefix_arr = [0] * 6
    prefix_arr[0] = 0
    for i in range(1, 6):
        prefix_arr[i] = prefix_arr[i-1] + (dur[order[i-1]] - 1)
    
    # Define k_hel, k_war, k_rey: positions of Helsinki (0), Warsaw (1), Reykjavik (4)
    k_hel = If(order[0] == 0, 0,
               If(order[1] == 0, 1,
                If(order[2] == 0, 2,
                 If(order[3] == 0, 3,
                  If(order[4] == 0, 4, 5)))))
    
    k_war = If(order[0] == 1, 0,
               If(order[1] == 1, 1,
                If(order[2] == 1, 2,
                 If(order[3] == 1, 3,
                  If(order[4] == 1, 4, 5)))))
    
    k_rey = If(order[0] == 4, 0,
               If(order[1] == 4, 1,
                If(order[2] == 4, 2,
                 If(order[3] == 4, 3,
                  If(order[4] == 4, 4, 5)))))
    
    # Start days: s = 1 + prefix_arr[k]
    s_hel = 1 + If(k_hel == 0, prefix_arr[0],
                If(k_hel == 1, prefix_arr[1],
                 If(k_hel == 2, prefix_arr[2],
                  If(k_hel == 3, prefix_arr[3],
                   If(k_hel == 4, prefix_arr[4], prefix_arr[5]))))
    
    s_war = 1 + If(k_war == 0, prefix_arr[0],
                If(k_war == 1, prefix_arr[1],
                 If(k_war == 2, prefix_arr[2],
                  If(k_war == 3, prefix_arr[3],
                   If(k_war == 4, prefix_arr[4], prefix_arr[5]))))
    
    s_rey = 1 + If(k_rey == 0, prefix_arr[0],
                If(k_rey == 1, prefix_arr[1],
                 If(k_rey == 2, prefix_arr[2],
                  If(k_rey == 3, prefix_arr[3],
                   If(k_rey == 4, prefix_arr[4], prefix_arr[5]))))
    
    # Constraints for start days
    s.add(Or(s_hel == 1, s_hel == 2))
    s.add(And(s_war >= 7, s_war <= 11))
    s.add(And(s_rey >= 7, s_rey <= 9))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        order_model = [m.evaluate(order[i]).as_long() for i in range(6)]
        
        # Compute start days for each city in the order
        start_days = [0] * 6
        prefix_sum = 0
        for k in range(6):
            start_days[k] = 1 + prefix_sum
            if k < 5:
                prefix_sum += dur[order_model[k]] - 1
        
        # Build itinerary
        itinerary_list = []
        for k in range(6):
            city_index = order_model[k]
            start = start_days[k]
            end = start + dur[city_index] - 1
            for d in range(start, end + 1):
                itinerary_list.append({"day": d, "place": cities[city_index]})
        
        # Output the itinerary as JSON
        result_dict = {"itinerary": itinerary_list}
        print(json.dumps(result_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()