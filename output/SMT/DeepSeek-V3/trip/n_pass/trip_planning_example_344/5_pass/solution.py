from z3 import *

def solve_itinerary():
    # Cities
    Valencia, Athens, Naples, Zurich = 0, 1, 2, 3
    cities = ['Valencia', 'Athens', 'Naples', 'Zurich']
    
    # Direct flights: adjacency list
    direct_flights = {
        Valencia: [Naples, Athens, Zurich],
        Athens: [Valencia, Naples, Zurich],
        Naples: [Valencia, Athens, Zurich],
        Zurich: [Naples, Athens, Valencia]
    }
    
    # Create Z3 variables for each day's city
    days = 20
    day_city = [Int(f'day_{i}_city') for i in range(1, days + 1)]
    
    s = Solver()
    
    # Each day's city must be 0, 1, 2, or 3
    for day in day_city:
        s.add(Or([day == c for c in [Valencia, Athens, Naples, Zurich]]))
    
    # Fixed constraints:
    # Athens between day 1 and 6 (inclusive)
    for i in range(6):  # days 1 to 6 (0-based index)
        s.add(day_city[i] == Athens)
    
    # Naples between day 16 and 20 (inclusive)
    for i in range(15, 20):  # days 16 to 20 (0-based index)
        s.add(day_city[i] == Naples)
    
    # Total days per city
    total_valencia = sum([If(day_city[i] == Valencia, 1, 0) for i in range(days)])
    total_athens = sum([If(day_city[i] == Athens, 1, 0) for i in range(days)])
    total_naples = sum([If(day_city[i] == Naples, 1, 0) for i in range(days)])
    total_zurich = sum([If(day_city[i] == Zurich, 1, 0) for i in range(days)])
    
    s.add(total_valencia == 6)
    s.add(total_athens == 6)
    s.add(total_naples == 5)
    s.add(total_zurich == 6)
    
    # Flight transitions: consecutive days can be the same or adjacent via direct flights
    for i in range(days - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        s.add(Or(
            current == next_day,
            *[And(current == c1, next_day == c2) for c1 in [Valencia, Athens, Naples, Zurich] 
              for c2 in direct_flights[c1]]
        ))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = model[day_city[0]].as_long()
        start_day = 1
        for i in range(1, days):
            if model[day_city[i]].as_long() != current_city:
                itinerary.append({
                    'day_range': f'Day {start_day}-{i}',
                    'place': cities[current_city]
                })
                current_city = model[day_city[i]].as_long()
                start_day = i + 1
        itinerary.append({
            'day_range': f'Day {start_day}-{days}',
            'place': cities[current_city]
        })
        
        # Verify totals
        val_days = sum(1 for entry in itinerary 
                    if entry['place'] == 'Valencia' 
                    for day in range(int(entry['day_range'].split('-')[0][4:]), 
                                    int(entry['day_range'].split('-')[1]) + 1))
        ath_days = sum(1 for entry in itinerary 
                    if entry['place'] == 'Athens' 
                    for day in range(int(entry['day_range'].split('-')[0][4:]), 
                                    int(entry['day_range'].split('-')[1]) + 1))
        nap_days = sum(1 for entry in itinerary 
                    if entry['place'] == 'Naples' 
                    for day in range(int(entry['day_range'].split('-')[0][4:]), 
                                    int(entry['day_range'].split('-')[1]) + 1))
        zur_days = sum(1 for entry in itinerary 
                    if entry['place'] == 'Zurich' 
                    for day in range(int(entry['day_range'].split('-')[0][4:]), 
                                    int(entry['day_range'].split('-')[1]) + 1))
        
        assert val_days == 6
        assert ath_days == 6
        assert nap_days == 5
        assert zur_days == 6
        
        # Verify fixed periods
        assert any(entry['place'] == 'Athens' and 
                  entry['day_range'] == 'Day 1-6' for entry in itinerary)
        assert any(entry['place'] == 'Naples' and 
                  entry['day_range'] == 'Day 16-20' for entry in itinerary)
        
        # Verify flight transitions
        transitions = []
        for i in range(len(itinerary) - 1):
            current = itinerary[i]['place']
            next_city = itinerary[i + 1]['place']
            if current != next_city:
                transitions.append((current, next_city))
        
        for (c1, c2) in transitions:
            assert cities.index(c2) in direct_flights[cities.index(c1)]
        
        return {'itinerary': itinerary}
    else:
        return "No valid itinerary found."

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))