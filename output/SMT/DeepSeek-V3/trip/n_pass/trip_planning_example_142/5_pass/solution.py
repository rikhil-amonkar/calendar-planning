from z3 import *

def solve_itinerary():
    s = Solver()

    # Days and cities
    days = range(1, 8)  # Days 1-7
    cities = ['Madrid', 'Dublin', 'Tallinn']
    city_idx = {city: i for i, city in enumerate(cities)}

    # Decision variables
    location = [Int(f'loc_{day}') for day in days]
    for day in days:
        s.add(location[day-1] >= 0, location[day-1] < len(cities))

    # Transition variables (flights between days)
    transition = [Bool(f'trans_{day}') for day in days[1:]]  # Days 2-7

    # Flight connections matrix
    connected = [
        [0, 1, 0],  # Madrid connects to Dublin
        [1, 0, 1],  # Dublin connects to Madrid and Tallinn
        [0, 1, 0]   # Tallinn connects to Dublin
    ]

    # Constraints
    for day in days[1:]:
        prev_day = day-2
        curr_day = day-1
        
        # If transitioning, must be connected cities
        s.add(Implies(transition[curr_day-1],
                     connected[location[prev_day]][location[curr_day]] == 1))
        
        # If not transitioning, stay in same city
        s.add(Implies(Not(transition[curr_day-1]),
                     location[curr_day] == location[prev_day]))

    # Count days in each city (including flight days)
    madrid_days = Sum([If(location[day-1] == city_idx['Madrid'], 1, 0) for day in days])
    dublin_days = Sum([If(location[day-1] == city_idx['Dublin'], 1, 0) for day in days])
    tallinn_days = Sum([If(location[day-1] == city_idx['Tallinn'], 1, 0) for day in days])

    s.add(madrid_days == 4)
    s.add(dublin_days == 3)
    s.add(tallinn_days == 2)

    # Workshop in Tallinn on day 6 or 7
    s.add(Or(location[5] == city_idx['Tallinn'],
             location[6] == city_idx['Tallinn']))

    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_stay = {'city': cities[m.evaluate(location[0]).as_long()], 'start': 1}
        
        for day in days[1:]:
            curr_city = cities[m.evaluate(location[day-1]).as_long()]
            is_transition = m.evaluate(transition[day-2])
            
            if is_transition:
                # Add previous stay
                if current_stay['start'] == day-1:
                    itinerary.append({'day': day-1, 'place': current_stay['city']})
                else:
                    itinerary.append({'day': f"{current_stay['start']}-{day-1}", 'place': current_stay['city']})
                
                # Add transition
                itinerary.append({'day': day, 'place': f"Fly from {current_stay['city']} to {curr_city}"})
                current_stay = {'city': curr_city, 'start': day+1}
            elif day == 7:
                # Last day
                if current_stay['start'] <= day:
                    if current_stay['start'] == day:
                        itinerary.append({'day': day, 'place': curr_city})
                    else:
                        itinerary.append({'day': f"{current_stay['start']}-{day}", 'place': curr_city})
        
        # Verify constraints
        counts = {'Madrid': 0, 'Dublin': 0, 'Tallinn': 0}
        workshop_ok = False
        
        for entry in itinerary:
            if 'Fly' not in entry['place']:
                for city in cities:
                    if city in entry['place']:
                        if '-' in str(entry['day']):
                            start, end = map(int, str(entry['day']).split('-'))
                            counts[city] += end - start + 1
                        else:
                            counts[city] += 1
                
                # Fixed workshop constraint check
                if 'Tallinn' in entry['place']:
                    if isinstance(entry['day'], int):
                        if entry['day'] in [6, 7]:
                            workshop_ok = True
                    else:
                        start, end = map(int, entry['day'].split('-'))
                        if (start <= 6 <= end) or (start <= 7 <= end):
                            workshop_ok = True
        
        if (counts['Madrid'] == 4 and counts['Dublin'] == 3 and 
            counts['Tallinn'] == 2 and workshop_ok):
            return {'itinerary': itinerary}
        else:
            return {"error": "Solution violates constraints", "counts": counts, "workshop": workshop_ok}
    else:
        return {"error": "No valid itinerary found"}

# Generate itinerary
itinerary = solve_itinerary()
print(itinerary)