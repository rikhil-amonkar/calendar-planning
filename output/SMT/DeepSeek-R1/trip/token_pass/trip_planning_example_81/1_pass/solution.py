import z3
import json

def main():
    # City constants
    M = 0  # Mykonos
    B = 1  # Budapest
    H = 2  # Hamburg
    n_days = 9
    city_names = {M: 'Mykonos', B: 'Budapest', H: 'Hamburg'}
    
    # Initialize solver
    s = z3.Solver()
    
    # Create variables for morning and evening cities for each day
    morning = [z3.Int('m_%d' % i) for i in range(1, n_days+1)]
    evening = [z3.Int('e_%d' % i) for i in range(1, n_days+1)]
    
    # Constraint: evening[i] = morning[i+1] for i in 0..7
    for i in range(n_days-1):
        s.add(evening[i] == morning[i+1])
    
    # All morning and evening values must be valid cities
    for i in range(n_days):
        s.add(z3.Or(morning[i] == M, morning[i] == B, morning[i] == H))
        s.add(z3.Or(evening[i] == M, evening[i] == B, evening[i] == H))
    
    # Define allowed flights
    allowed_flights = [(B, M), (M, B), (H, B), (B, H)]
    for i in range(n_days):
        flight_taken = (morning[i] != evening[i])
        constraints = []
        for (c1, c2) in allowed_flights:
            constraints.append(z3.And(morning[i] == c1, evening[i] == c2))
        s.add(z3.Implies(flight_taken, z3.Or(constraints)))
    
    # Count days per city
    def count_city(c):
        return z3.Sum([
            z3.If(z3.Or(morning[i] == c, evening[i] == c), 1, 0)
            for i in range(n_days)
        ])
    
    s.add(count_city(M) == 6)
    s.add(count_city(B) == 3)
    s.add(count_city(H) == 2)
    
    # Conference constraints: entire days in Mykonos on day 4 and day 9
    s.add(morning[3] == M)  # Day 4 morning
    s.add(evening[3] == M)  # Day 4 evening
    s.add(morning[8] == M)  # Day 9 morning
    s.add(evening[8] == M)  # Day 9 evening
    
    # Solve
    if s.check() == z3.sat:
        model = s.model()
        morning_vals = [model.eval(morning[i]).as_long() for i in range(n_days)]
        evening_vals = [model.eval(evening[i]).as_long() for i in range(n_days)]
        
        # Create time slots
        time_slots = []
        for day in range(1, n_days+1):
            time_slots.append(('morning', day, morning_vals[day-1]))
            time_slots.append(('evening', day, evening_vals[day-1]))
        
        # Group consecutive slots in same city
        segments = []
        current_segment = None
        
        def next_slot(slot):
            day, part = slot
            if part == 'morning':
                return (day, 'evening')
            else:
                return (day+1, 'morning')
        
        for slot in time_slots:
            part, day, city = slot
            if current_segment is None:
                current_segment = {
                    'start': (day, part),
                    'end': (day, part),
                    'city': city
                }
            else:
                current_end = current_segment['end']
                if current_segment['city'] == city and next_slot(current_end) == (day, part):
                    current_segment['end'] = (day, part)
                else:
                    segments.append(current_segment)
                    current_segment = {
                        'start': (day, part),
                        'end': (day, part),
                        'city': city
                    }
        if current_segment is not None:
            segments.append(current_segment)
        
        # Convert segments to itinerary format
        itinerary = []
        for seg in segments:
            start_day, start_part = seg['start']
            end_day, end_part = seg['end']
            city = city_names[seg['city']]
            
            if start_day == end_day:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()