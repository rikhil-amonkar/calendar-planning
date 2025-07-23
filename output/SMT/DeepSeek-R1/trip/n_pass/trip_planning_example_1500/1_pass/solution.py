from z3 import *
import json

def main():
    cities = ['London', 'Milan', 'Zurich', 'Reykjavik', 'Bucharest', 'Hamburg', 'Barcelona', 'Stuttgart', 'Stockholm', 'Tallinn']
    fixed_end_city = [0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3]  # Days 1 to 13 (indices 0 to 12)

    end_city = [Int('end_city_%d' % i) for i in range(28)]
    s = Solver()
    
    for i in range(13):
        s.add(end_city[i] == fixed_end_city[i])
    
    for i in range(13, 28):
        s.add(end_city[i] >= 4, end_city[i] <= 9)
    
    flights_str = [
        (0,5), (0,3), (1,6), (3,6), (3,7), (8,3), (0,7), (1,2), (0,6), (8,5),
        (2,6), (8,7), (1,5), (8,9), (5,4), (0,4), (1,8), (7,5), (0,2), (1,3),
        (0,8), (1,7), (8,6), (0,1), (2,5), (4,6), (2,8), (6,9), (2,9), (5,6),
        (7,6), (2,3), (2,4)
    ]
    directed_pairs = []
    for (a, b) in flights_str:
        directed_pairs.append((a, b))
        directed_pairs.append((b, a))
    
    for i in range(1, 28):
        from_city = end_city[i-1]
        to_city = end_city[i]
        flight_possible = Or([And(from_city == a, to_city == b) for (a, b) in directed_pairs])
        s.add(If(from_city != to_city, flight_possible, True))
    
    total_days = [0] * 10
    for c in range(10):
        total = 0
        for i in range(0, 28):
            if i == 0:
                in_city = Or(0 == c, end_city[0] == c)
            else:
                in_city = Or(end_city[i-1] == c, end_city[i] == c)
            total += If(in_city, 1, 0)
        total_days[c] = total
    
    s.add(total_days[0] == 3)  # London
    s.add(total_days[1] == 5)  # Milan
    s.add(total_days[2] == 2)  # Zurich
    s.add(total_days[3] == 5)  # Reykjavik
    s.add(total_days[4] == 2)  # Bucharest
    s.add(total_days[5] == 5)  # Hamburg
    s.add(total_days[6] == 4)  # Barcelona
    s.add(total_days[7] == 5)  # Stuttgart
    s.add(total_days[8] == 2)  # Stockholm
    s.add(total_days[9] == 4)  # Tallinn
    
    travel_days_last15 = 0
    for i in range(13, 28):
        travel_day = end_city[i-1] != end_city[i]
        travel_days_last15 += If(travel_day, 1, 0)
    s.add(travel_days_last15 == 7)
    
    if s.check() == sat:
        m = s.model()
        res = [m.evaluate(end_city[i]).as_long() for i in range(28)]
        itinerary = []
        for i in range(28):
            if i == 0:
                start = 0
            else:
                start = res[i-1]
            end = res[i]
            if start == end:
                itinerary.append([cities[start]])
            else:
                itinerary.append([cities[start], cities[end]])
        result_dict = {'itinerary': itinerary}
        print(json.dumps(result_dict))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()