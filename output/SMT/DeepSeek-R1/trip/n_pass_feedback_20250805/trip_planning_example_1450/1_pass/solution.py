from z3 import *
import json

def main():
    # City names and their required days
    cities = ['Stockholm', 'Hamburg', 'Florence', 'Istanbul', 'Oslo', 'Vilnius', 'Santorini', 'Munich', 'Frankfurt', 'Krakow']
    req = [3, 5, 2, 5, 5, 5, 2, 5, 4, 5]  # Corresponding to the cities list

    # Create Z3 variables for the sequence of cities (c0 to c9)
    c = [Int(f'c{i}') for i in range(10)]
    s = Solver()

    # Constraint: each c[i] is between 0 and 9
    for i in range(10):
        s.add(And(c[i] >= 0, c[i] < 10))
    s.add(Distinct(c))

    # Define prefix sums for cumulative days
    prefix = [Int(f'prefix{i}') for i in range(10)]
    s.add(prefix[0] == req[c[0]])
    for i in range(1, 10):
        s.add(prefix[i] == prefix[i-1] + req[c[i]])

    # Constraints for fixed events
    # Krakow (index 9) must be at position k (1<=k<=9) with cumulative sum at k-1 equal to (k-1) + 5
    # Istanbul (index 3) must be at position j (1<=j<=9) with cumulative sum at j-1 equal to (j-1) + 25
    for pos in range(1, 10):
        s.add(Implies(c[pos] == 9, prefix[pos-1] - (pos-1) == 5))
        s.add(Implies(c[pos] == 3, prefix[pos-1] - (pos-1) == 25))

    # Define the directed flight graph
    bidirectional = [
        (0,4), (4,0),
        (9,8), (8,9),
        (9,3), (3,9),
        (7,0), (0,7),
        (1,0), (0,1),
        (4,3), (3,4),
        (3,0), (0,3),
        (4,9), (9,4),
        (5,3), (3,5),
        (4,8), (8,4),
        (8,2), (2,8),
        (8,7), (7,8),
        (4,1), (1,4),
        (5,8), (8,5),
        (9,7), (7,9),
        (1,3), (3,1),
        (8,0), (0,8),
        (7,1), (1,7)
    ]
    directed = [
        (9,5),
        (2,7),
        (0,6),
        (6,4),
        (5,7)
    ]
    edges = bidirectional + directed

    # Flight constraints: consecutive cities must have a valid flight
    for i in range(9):
        s.add(Or([And(c[i] == u, c[i+1] == v) for (u, v) in edges]))

    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        c_val = [m.evaluate(c[i]).as_long() for i in range(10)]
        
        # Compute departure days (d0 to d8)
        dep = [0] * 9
        dep[0] = req[c_val[0]]
        for i in range(1, 9):
            dep[i] = dep[i-1] + req[c_val[i]] - 1
        
        # Build itinerary
        itinerary_list = []
        for day in range(1, 33):
            # Segment 0: city0 from day 1 to dep[0]
            if day <= dep[0]:
                itinerary_list.append({'day': day, 'place': cities[c_val[0]]})
            # Segment 1: city1 from dep[0] to dep[1]
            if dep[0] <= day <= dep[1]:
                itinerary_list.append({'day': day, 'place': cities[c_val[1]]})
            # Segment 2: city2 from dep[1] to dep[2]
            if dep[1] <= day <= dep[2]:
                itinerary_list.append({'day': day, 'place': cities[c_val[2]]})
            # Segment 3: city3 from dep[2] to dep[3]
            if dep[2] <= day <= dep[3]:
                itinerary_list.append({'day': day, 'place': cities[c_val[3]]})
            # Segment 4: city4 from dep[3] to dep[4]
            if dep[3] <= day <= dep[4]:
                itinerary_list.append({'day': day, 'place': cities[c_val[4]]})
            # Segment 5: city5 from dep[4] to dep[5]
            if dep[4] <= day <= dep[5]:
                itinerary_list.append({'day': day, 'place': cities[c_val[5]]})
            # Segment 6: city6 from dep[5] to dep[6]
            if dep[5] <= day <= dep[6]:
                itinerary_list.append({'day': day, 'place': cities[c_val[6]]})
            # Segment 7: city7 from dep[6] to dep[7]
            if dep[6] <= day <= dep[7]:
                itinerary_list.append({'day': day, 'place': cities[c_val[7]]})
            # Segment 8: city8 from dep[7] to dep[8]
            if dep[7] <= day <= dep[8]:
                itinerary_list.append({'day': day, 'place': cities[c_val[8]]})
            # Segment 9: city9 from dep[8] to day 32
            if day >= dep[8]:
                itinerary_list.append({'day': day, 'place': cities[c_val[9]]})
        
        # Output as JSON
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()