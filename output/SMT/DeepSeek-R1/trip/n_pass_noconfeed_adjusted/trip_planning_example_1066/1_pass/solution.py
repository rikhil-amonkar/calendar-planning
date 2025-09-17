import json
from z3 import *

def main():
    # City mapping
    cities = {
        'Brussels': 0,
        'Bucharest': 1,
        'Stuttgart': 2,
        'Mykonos': 3,
        'Madrid': 4,
        'Helsinki': 5,
        'Split': 6,
        'London': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Required days per city
    required_days = {
        cities['Brussels']: 4,
        cities['Bucharest']: 3,
        cities['Stuttgart']: 4,
        cities['Mykonos']: 2,
        cities['Madrid']: 2,
        cities['Helsinki']: 5,
        cities['Split']: 3,
        cities['London']: 5
    }
    
    # Direct flights (undirected)
    flights = [
        (cities['Helsinki'], cities['London']),
        (cities['Split'], cities['Madrid']),
        (cities['Helsinki'], cities['Madrid']),
        (cities['London'], cities['Madrid']),
        (cities['Brussels'], cities['London']),
        (cities['Bucharest'], cities['London']),
        (cities['Brussels'], cities['Bucharest']),
        (cities['Bucharest'], cities['Madrid']),
        (cities['Split'], cities['Helsinki']),
        (cities['Mykonos'], cities['Madrid']),
        (cities['Stuttgart'], cities['London']),
        (cities['Helsinki'], cities['Brussels']),
        (cities['Brussels'], cities['Madrid']),
        (cities['Split'], cities['London']),
        (cities['Stuttgart'], cities['Split']),
        (cities['London'], cities['Mykonos'])
    ]
    
    # Create solver
    s = Solver()
    
    # Evening city for days 0 to 21
    e = IntVector('e', 22)
    
    # Constrain each e[i] to be between 0 and 7
    for i in range(22):
        s.add(And(e[i] >= 0, e[i] <= 7))
    
    # Constrain direct flights for transitions
    for i in range(1, 22):
        # If evening city changes, ensure there's a direct flight
        s.add(If(e[i-1] != e[i], 
                 Or([And(e[i-1] == a, e[i] == b) for a, b in flights] + 
                    [And(e[i-1] == b, e[i] == a) for a, b in flights]),
                 True))
    
    # Function to compute total days for a city
    def total_days(city):
        return Sum([If(Or(e[i-1] == city, e[i] == city), 1, 0) for i in range(1, 22)])
    
    # Add constraints for required days per city
    for city, days in required_days.items():
        s.add(total_days(city) == days)
    
    # Constraint: Stuttgart between day 1 and 4
    stuttgart_constraint = Or([Or(e[i-1] == cities['Stuttgart'], e[i] == cities['Stuttgart']) for i in range(1, 5)])
    s.add(stuttgart_constraint)
    
    # Madrid constraints: must be in Madrid on evening of day 20 and 21
    s.add(e[20] == cities['Madrid'])
    s.add(e[21] == cities['Madrid'])
    # Ensure not in Madrid on other days (since total days must be 2)
    # Already handled by total_days constraint
    
    # Check satisfaction
    if s.check() == sat:
        m = s.model()
        eval_e = [m.eval(e[i]).as_long() for i in range(22)]
        
        # Generate events
        events = []
        # Day 1
        if eval_e[0] != eval_e[1]:
            events.append(('1', '1', city_names[eval_e[0]]))  # Morning
            events.append(('1', '1', city_names[eval_e[1]]))  # Evening
        else:
            events.append(('1', '1', city_names[eval_e[1]]))  # Whole day
        
        # Days 2 to 21
        for day in range(2, 22):
            if eval_e[day-1] != eval_e[day]:
                events.append((str(day), str(day), city_names[eval_e[day-1]]))  # Morning
                events.append((str(day), str(day), city_names[eval_e[day]]))    # Evening
            else:
                events.append((str(day), str(day), city_names[eval_e[day]]))    # Whole day
        
        # Group events into continuous stays
        itinerary = []
        i = 0
        while i < len(events):
            start_day, end_day, city = events[i]
            j = i + 1
            # Group consecutive whole-day events for the same city
            while j < len(events) and events[j][2] == city and events[j][0] == events[j][1] and events[j][0] == str(int(end_day) + 1):
                end_day = events[j][1]
                j += 1
            if start_day == end_day:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city})
            i = j
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()