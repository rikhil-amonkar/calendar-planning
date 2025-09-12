import json
from z3 import *

def main():
    # Cities and their required days
    cities = ['IST', 'VIE', 'RIX', 'BRU', 'MAD', 'VNO', 'VCE', 'GVA', 'MUC', 'RKV']
    required_days = {
        'IST': 4,
        'VIE': 4,
        'RIX': 2,
        'BRU': 2,
        'MAD': 4,
        'VNO': 4,
        'VCE': 5,
        'GVA': 4,
        'MUC': 5,
        'RKV': 2
    }
    
    # Event constraints: city -> list of days
    event_days = {
        'BRU': [26, 27],
        'VNO': [20, 21, 22, 23],
        'VCE': [7, 8, 9, 10, 11],
        'GVA': [1, 2, 3, 4]
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ('MUC', 'VIE'), ('IST', 'BRU'), ('VIE', 'VNO'), ('MAD', 'MUC'), ('VCE', 'BRU'), ('RIX', 'BRU'),
        ('GVA', 'IST'), ('MUC', 'RKV'), ('VIE', 'IST'), ('RIX', 'IST'), ('RKV', 'VIE'), ('VCE', 'MUC'),
        ('MAD', 'VCE'), ('VNO', 'IST'), ('VCE', 'VIE'), ('VCE', 'IST'), ('RKV', 'MAD'), ('RIX', 'MUC'),
        ('MUC', 'IST'), ('RKV', 'BRU'), ('VNO', 'BRU'), ('VNO', 'MUC'), ('MAD', 'VIE'), ('VIE', 'RIX'),
        ('GVA', 'VIE'), ('MAD', 'BRU'), ('VIE', 'BRU'), ('GVA', 'BRU'), ('GVA', 'MAD'), ('MUC', 'BRU'),
        ('MAD', 'IST'), ('GVA', 'MUC'), ('RIX', 'VNO')
    ]
    direct_flights_set = set()
    for (a, b) in direct_flights:
        direct_flights_set.add((a, b))
        direct_flights_set.add((b, a))
    
    n_days = 27
    n_cities = len(cities)
    
    # Create solver
    s = Solver()
    
    # Create variables: for each day and city, a Boolean indicating presence
    in_vars = [[Bool(f"in_{day}_{city}") for city in cities] for day in range(1, n_days+1)]
    
    # Constraint 1: Each day has at least one and at most two cities
    for day in range(n_days):
        day_vars = in_vars[day]
        s.add(AtLeast(*day_vars, 1))
        s.add(AtMost(*day_vars, 2))
    
    # Constraint 2: Total days per city matches requirement
    for c_idx, city in enumerate(cities):
        total = 0
        for day in range(n_days):
            total += If(in_vars[day][c_idx], 1, 0)
        s.add(total == required_days[city])
    
    # Constraint 3: Event constraints
    for city, days in event_days.items():
        c_idx = cities.index(city)
        for d in days:
            s.add(in_vars[d-1][c_idx] == True)
    
    # Constraint 4: If two cities on same day, they must have direct flight
    for day in range(n_days):
        for i in range(n_cities):
            for j in range(i+1, n_cities):
                city_i = cities[i]
                city_j = cities[j]
                if (city_i, city_j) not in direct_flights_set:
                    s.add(Not(And(in_vars[day][i], in_vars[day][j])))
    
    # Constraint 5: Consecutive days must share at least one city
    for day in range(n_days-1):
        day1_vars = in_vars[day]
        day2_vars = in_vars[day+1]
        common = Or([And(day1_vars[i], day2_vars[i]) for i in range(n_cities)])
        s.add(common)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        # Create a presence matrix: days x cities -> True/False
        presence = []
        for day in range(n_days):
            day_presence = []
            for c_idx in range(n_cities):
                day_presence.append(is_true(m.evaluate(in_vars[day][c_idx])))
            presence.append(day_presence)
        
        # For each city, find continuous intervals
        itinerary = []
        for c_idx, city in enumerate(cities):
            in_city = [presence[day][c_idx] for day in range(n_days)]
            start = None
            for day in range(n_days):
                if in_city[day] and start is None:
                    start = day
                if not in_city[day] and start is not None:
                    end = day - 1
                    if start == end:
                        day_range = f"Day {start+1}"
                    else:
                        day_range = f"Day {start+1}-{end+1}"
                    itinerary.append({"day_range": day_range, "place": city})
                    start = None
            if start is not None:
                end = n_days - 1
                if start == end:
                    day_range = f"Day {start+1}"
                else:
                    day_range = f"Day {start+1}-{end+1}"
                itinerary.append({"day_range": day_range, "place": city})
        
        # Sort itinerary by the first day of the range
        def get_first_day(entry):
            parts = entry['day_range'].split(' ')[1]
            if '-' in parts:
                return int(parts.split('-')[0])
            return int(parts)
        
        itinerary.sort(key=get_first_day)
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()