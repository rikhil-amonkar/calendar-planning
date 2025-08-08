from z3 import *

def main():
    city_names = ['Prague', 'Tallinn', 'Warsaw', 'Porto', 'Naples', 'Milan', 'Lisbon', 'Santorini', 'Riga', 'Stockholm']
    L = [5, 3, 2, 3, 5, 3, 5, 5, 4, 2]  # lengths of stay for each city

    # Build allowed_edges_set as a set of tuples (i, j) for directed flights
    allowed_edges_set = set()
    # Bidirectional edges
    bidirectional = [
        (8, 0), (0, 8),    # Riga and Prague
        (9, 5), (5, 9),    # Stockholm and Milan
        (8, 5), (5, 8),    # Riga and Milan
        (6, 9), (9, 6),    # Lisbon and Stockholm
        (4, 2), (2, 4),    # Naples and Warsaw
        (6, 2), (2, 6),    # Lisbon and Warsaw
        (4, 5), (5, 4),    # Naples and Milan
        (6, 4), (4, 6),    # Lisbon and Naples
        (1, 0), (0, 1),    # Tallinn and Prague
        (9, 2), (2, 9),    # Stockholm and Warsaw
        (8, 2), (2, 8),    # Riga and Warsaw
        (6, 8), (8, 6),    # Lisbon and Riga
        (8, 9), (9, 8),    # Riga and Stockholm
        (6, 3), (3, 6),    # Lisbon and Porto
        (6, 0), (0, 6),    # Lisbon and Prague
        (5, 3), (3, 5),    # Milan and Porto
        (0, 5), (5, 0),    # Prague and Milan
        (6, 5), (5, 6),    # Lisbon and Milan
        (2, 3), (3, 2),    # Warsaw and Porto
        (2, 1), (1, 2),    # Warsaw and Tallinn
        (7, 5), (5, 7),    # Santorini and Milan
        (9, 0), (0, 9),    # Stockholm and Prague
        (9, 1), (1, 9),    # Stockholm and Tallinn
        (2, 5), (5, 2),    # Warsaw and Milan
        (7, 4), (4, 7),    # Santorini and Naples
        (2, 0), (0, 2)     # Warsaw and Prague
    ]
    # Unidirectional edges
    unidirectional = [
        (9, 7),    # from Stockholm to Santorini
        (8, 1)      # from Riga to Tallinn
    ]
    for edge in bidirectional:
        allowed_edges_set.add(edge)
    for edge in unidirectional:
        allowed_edges_set.add(edge)
    
    allowed_edges_matrix = [[(i, j) in allowed_edges_set for j in range(10)] for i in range(10)]

    # Create Z3 solver and variables
    s = Solver()
    Order = [Int('order_%d' % i) for i in range(10)]
    
    # Constraints: each Order[i] between 0 and 9, and all distinct
    for i in range(10):
        s.add(Order[i] >= 0, Order[i] <= 9)
    s.add(Distinct(Order))
    
    # Define prev_sum for each city: sum of lengths of cities with lower order
    prev_sum = [Int('prev_sum_%d' % i) for i in range(10)]
    for i in range(10):
        s.add(prev_sum[i] == Sum([If(Order[j] < Order[i], L[j], 0) for j in range(10)]))
    
    # Constraints for Riga (index 8): start day = 5
    s.add(prev_sum[8] - Order[8] == 4)  # because 1 + prev_sum[8] - Order[8] = 5
    
    # Constraints for Tallinn (index 1): start day between 16 and 20
    s.add(prev_sum[1] - Order[1] >= 15, prev_sum[1] - Order[1] <= 19)
    
    # Constraints for Milan (index 5): start day between 22 and 24
    s.add(prev_sum[5] - Order[5] >= 21, prev_sum[5] - Order[5] <= 23)
    
    # Flight constraints: for disallowed edges, ensure they are not consecutive
    for i in range(10):
        for j in range(10):
            if i != j and not allowed_edges_matrix[i][j]:
                s.add(Not(And(Order[i] < 9, Order[j] == Order[i] + 1)))
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        order_vals = [model.evaluate(Order[i]).as_long() for i in range(10)]
        
        # Compute start days for each city
        start_days = [0] * 10
        for i in range(10):
            prev_sum_val = 0
            for j in range(10):
                if order_vals[j] < order_vals[i]:
                    prev_sum_val += L[j]
            start_days[i] = 1 + prev_sum_val - order_vals[i]
        
        # Build itinerary
        itinerary_list = []
        for d in range(1, 29):  # days 1 to 28
            cities_today = []  # (order_val, city_index)
            for i in range(10):
                start = start_days[i]
                end = start + L[i] - 1
                if start <= d <= end:
                    cities_today.append((order_vals[i], i))
            # Sort cities by order value to ensure departure before arrival on travel days
            cities_today_sorted = sorted(cities_today, key=lambda x: x[0])
            for _, idx in cities_today_sorted:
                itinerary_list.append({"day": d, "city": city_names[idx]})
        
        # Output as JSON
        print({
            "itinerary": itinerary_list
        })
    else:
        print("No solution found")

if __name__ == "__main__":
    main()