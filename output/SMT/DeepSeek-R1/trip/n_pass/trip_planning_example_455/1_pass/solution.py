from z3 import *
import json

def main():
    s = Solver()
    
    # Define the days: 21 days (day1 to day21)
    Start = [ Int('Start_%d' % d) for d in range(1, 22) ]
    End   = [ Int('End_%d' % d) for d in range(1, 22) ]
    
    # City mapping
    cities = {
        0: 'Reykjavik',
        1: 'Riga',
        2: 'Warsaw',
        3: 'Istanbul',
        4: 'Krakow'
    }
    required_days = [7, 2, 3, 6, 7]  # Reykjavik, Riga, Warsaw, Istanbul, Krakow
    
    # Allowed flight pairs: same city and direct flights (both directions)
    allowed_pairs = set()
    for c in range(5):
        allowed_pairs.add((c, c))
    edges = [(0,2), (2,0), (1,2), (2,1), (1,3), (3,1), (2,3), (3,2), (2,4), (4,2), (3,4), (4,3)]
    for a, b in edges:
        allowed_pairs.add((a, b))
    
    # Constraints for each day
    for i in range(21):
        s.add(Start[i] >= 0, Start[i] <= 4)
        s.add(End[i] >= 0, End[i] <= 4)
        s.add(Or([And(Start[i] == a, End[i] == b) for (a, b) in allowed_pairs]))
    
    # Chain constraints: Start of day i+1 equals End of day i
    for i in range(1, 21):
        s.add(Start[i] == End[i-1])
    
    # Total days per city
    for c in range(5):
        total = 0
        for i in range(21):
            total += If(Or(Start[i] == c, End[i] == c), 1, 0)
        s.add(total == required_days[c])
    
    # Riga meeting constraint (day1 or day2)
    s.add(Or(Or(Start[0] == 1, End[0] == 1), Or(Start[1] == 1, End[1] == 1)))
    
    # Istanbul wedding constraint (day2 to day7)
    constraints = []
    for i in range(1, 7):  # days 2 to 7 (indices 1 to 6)
        constraints.append(Or(Start[i] == 3, End[i] == 3))
    s.add(Or(constraints))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(21):
            day = i + 1
            start_city_val = m[Start[i]].as_long()
            end_city_val = m[End[i]].as_long()
            if start_city_val == end_city_val:
                itinerary.append({"day": day, "place": cities[start_city_val]})
            else:
                itinerary.append({"day": day, "place": cities[start_city_val]})
                itinerary.append({"day": day, "place": cities[end_city_val]})
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()