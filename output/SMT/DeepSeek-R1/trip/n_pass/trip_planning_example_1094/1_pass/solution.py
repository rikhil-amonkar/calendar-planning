from z3 import *
import json

def main():
    # Define the days and cities
    days = list(range(1, 17))
    cities = sorted(['Vienna', 'Barcelona', 'Edinburgh', 'Krakow', 'Riga', 'Hamburg', 'Paris', 'Stockholm'])
    
    # Direct flights processing
    flight_str = "Hamburg and Stockholm, Vienna and Stockholm, Paris and Edinburgh, Riga and Barcelona, Paris and Riga, Krakow and Barcelona, Edinburgh and Stockholm, Paris and Krakow, Krakow and Stockholm, Riga and Edinburgh, Barcelona and Stockholm, Paris and Stockholm, Krakow and Edinburgh, Vienna and Hamburg, Paris and Hamburg, Riga and Stockholm, Hamburg and Barcelona, Vienna and Barcelona, Krakow and Vienna, from Riga to Hamburg, Barcelona and Edinburgh, Paris and Barcelona, Hamburg and Edinburgh, Paris and Vienna, Vienna and Riga"
    flight_str = flight_str.rstrip('.')
    parts = flight_str.split(', ')
    flight_pairs = []
    for p in parts:
        if p.startswith('from'):
            words = p.split()
            flight_pairs.append((words[1], words[3]))
        else:
            a, b = p.split(' and ')
            flight_pairs.append((a, b))
    
    direct_flights_set = set()
    for (a, b) in flight_pairs:
        direct_flights_set.add(frozenset({a, b}))
    
    # Create Z3 solver and variables
    s = Solver()
    in_city = {}
    for d in days:
        for c in cities:
            in_city[(d, c)] = Bool(f"in_{d}_{c}")
    
    # Constraints for each day
    for d in days:
        # At least one city per day
        s.add(Or([in_city[(d, c)] for c in cities]))
        # At most two cities per day
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    c1, c2, c3 = cities[i], cities[j], cities[k]
                    s.add(Not(And(in_city[(d, c1)], in_city[(d, c2)], in_city[(d, c3)]))
        # If two cities, they must be connected by a direct flight
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1, c2 = cities[i], cities[j]
                if frozenset({c1, c2}) not in direct_flights_set:
                    s.add(Not(And(in_city[(d, c1)], in_city[(d, c2)])))
    
    # Fixed days
    s.add(in_city[(1, 'Paris')])
    s.add(in_city[(2, 'Paris')])
    s.add(in_city[(10, 'Hamburg')])
    s.add(in_city[(11, 'Hamburg')])
    s.add(in_city[(15, 'Stockholm')])
    s.add(in_city[(16, 'Stockholm')])
    
    # Total days per city
    required_days = {
        'Vienna': 4,
        'Barcelona': 2,
        'Edinburgh': 4,
        'Krakow': 3,
        'Riga': 4,
        'Hamburg': 2,
        'Paris': 2,
        'Stockholm': 2
    }
    for c in cities:
        total = Sum([If(in_city[(d, c)], 1, 0) for d in days])
        s.add(total == required_days[c])
    
    # Continuity between consecutive days
    for d in range(2, 17):
        s.add(Or([And(in_city[(d-1, c)], in_city[(d, c)]) for c in cities]))
    
    # Edinburgh meeting between day 12 and 15
    s.add(Or([in_city[(d, 'Edinburgh')] for d in range(12, 16)]))
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        events = []
        # Collect contiguous blocks for each city
        for city in cities:
            city_days = []
            for d in days:
                if is_true(model[in_city[(d, city)]]):
                    city_days.append(d)
            if not city_days:
                continue
            intervals = []
            start = city_days[0]
            end = city_days[0]
            for i in range(1, len(city_days)):
                if city_days[i] == end + 1:
                    end = city_days[i]
                else:
                    intervals.append((start, end))
                    start = city_days[i]
                    end = city_days[i]
            intervals.append((start, end))
            for (s_int, e_int) in intervals:
                if s_int == e_int:
                    day_range_str = f"Day {s_int}"
                else:
                    day_range_str = f"Day {s_int}-{e_int}"
                events.append((s_int, 1, day_range_str, city))
        # Collect flight day records
        for d in days:
            cities_on_d = []
            for city in cities:
                if is_true(model[in_city[(d, city)]]):
                    cities_on_d.append(city)
            if len(cities_on_d) == 2:
                for city in sorted(cities_on_d):
                    events.append((d, 0, f"Day {d}", city))
        # Sort events: by day, then by type (0 for flight, 1 for block), then by city
        events_sorted = sorted(events, key=lambda x: (x[0], x[1], x[3]))
        itinerary = [{"day_range": day_range, "place": place} for (_, _, day_range, place) in events_sorted]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()