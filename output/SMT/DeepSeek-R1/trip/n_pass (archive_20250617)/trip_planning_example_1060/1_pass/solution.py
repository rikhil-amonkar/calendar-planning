from z3 import *

def main():
    # Cities mapping
    cities = {
        0: 'Reykjavik',
        1: 'Stuttgart',
        2: 'Istanbul',
        3: 'Vilnius',
        4: 'Seville',
        5: 'Geneva',
        6: 'Valencia',
        7: 'Munich'
    }
    
    # Directed flights: list of tuples (from, to)
    flights = [
        (0, 7), (7, 0),  # Reykjavik <-> Munich
        (0, 1),           # Reykjavik -> Stuttgart
        (1, 6), (6, 1),   # Stuttgart <-> Valencia
        (1, 2), (2, 1),   # Stuttgart <-> Istanbul
        (7, 5), (5, 7),   # Munich <-> Geneva
        (2, 3), (3, 2),   # Istanbul <-> Vilnius
        (6, 4), (4, 6),   # Valencia <-> Seville
        (6, 2), (2, 6),   # Valencia <-> Istanbul
        (3, 7),           # Vilnius -> Munich
        (4, 7), (7, 4),   # Seville <-> Munich
        (7, 2), (2, 7),   # Munich <-> Istanbul
        (6, 5), (5, 6),   # Valencia <-> Geneva
        (6, 7), (7, 6),   # Valencia <-> Munich
        (5, 2), (2, 5)    # Geneva <-> Istanbul
    ]
    
    s = Solver()
    
    # 25 days, each day's end city (0 to 7)
    c = [Int('c_%d' % i) for i in range(25)]
    
    # Each day's city must be between 0 and 7
    for i in range(25):
        s.add(And(c[i] >= 0, c[i] <= 7))
    
    # Day 1 must be Reykjavik
    s.add(c[0] == 0)
    
    # Flight constraints: if city changes, there must be a direct flight
    for i in range(1, 25):
        prev = c[i-1]
        curr = c[i]
        flight_taken = (prev != curr)
        allowed_flight = Or([And(prev == f, curr == t) for (f, t) in flights])
        s.add(If(flight_taken, allowed_flight, True))
    
    # Define presence in a city on a day
    def in_city(day_idx, city_idx):
        if day_idx == 0:
            return c[0] == city_idx
        else:
            return Or(c[day_idx] == city_idx, And(c[day_idx] != c[day_idx-1], c[day_idx-1] == city_idx))
    
    # Total days per city
    total_days = [0] * 8
    for j in range(8):
        total_days[j] = Sum([If(in_city(i, j), 1, 0) for i in range(25)])
    
    s.add(total_days[0] == 4)  # Reykjavik
    s.add(total_days[1] == 4)  # Stuttgart
    s.add(total_days[2] == 4)  # Istanbul
    s.add(total_days[3] == 4)  # Vilnius
    s.add(total_days[4] == 3)  # Seville
    s.add(total_days[5] == 5)  # Geneva
    s.add(total_days[6] == 5)  # Valencia
    s.add(total_days[7] == 3)  # Munich
    
    # Fixed events: specific cities on specific days
    s.add(in_city(3, 1))   # Stuttgart on day 4 (index 3)
    s.add(in_city(6, 1))   # Stuttgart on day 7 (index 6)
    s.add(in_city(12, 7))  # Munich on day 13 (index 12)
    s.add(in_city(13, 7))  # Munich on day 14 (index 13)
    s.add(in_city(14, 7))  # Munich on day 15 (index 14)
    s.add(in_city(18, 2))  # Istanbul on day 19 (index 18)
    s.add(in_city(19, 2))  # Istanbul on day 20 (index 19)
    s.add(in_city(20, 2))  # Istanbul on day 21 (index 20)
    s.add(in_city(21, 2))  # Istanbul on day 22 (index 21)
    s.add(in_city(0, 0))   # Reykjavik on day 1 (index 0)
    s.add(in_city(1, 0))   # Reykjavik on day 2 (index 1)
    s.add(in_city(2, 0))   # Reykjavik on day 3 (index 2)
    s.add(in_city(3, 0))   # Reykjavik on day 4 (index 3)
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        seq = [m.evaluate(c[i]).as_long() for i in range(25)]
        
        # Generate the itinerary
        itinerary = []
        for day in range(25):
            current_day = day + 1
            if day == 0:
                cities_today = [cities[seq[0]]]
            else:
                if seq[day] == seq[day - 1]:
                    cities_today = [cities[seq[day]]]
                else:
                    cities_today = [cities[seq[day - 1]], cities[seq[day]]]
            itinerary.append((current_day, cities_today))
        
        # Print the itinerary
        for day, cities_list in itinerary:
            print(f"Day {day}: {', '.join(cities_list)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()