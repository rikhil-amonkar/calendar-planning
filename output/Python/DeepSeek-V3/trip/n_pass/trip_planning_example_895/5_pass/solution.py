import json
from itertools import permutations

def find_itinerary():
    # Cities and required days
    cities = {
        'Brussels': 2,
        'Venice': 3,
        'London': 3,
        'Lisbon': 4,
        'Reykjavik': 3,
        'Santorini': 3,
        'Madrid': 5
    }
    
    # Direct flights
    flights = {
        'Venice': ['Madrid', 'Brussels', 'Santorini', 'Lisbon', 'London'],
        'Lisbon': ['Reykjavik', 'Venice', 'London', 'Madrid', 'Brussels'],
        'Brussels': ['Venice', 'London', 'Lisbon', 'Reykjavik', 'Madrid'],
        'Reykjavik': ['Lisbon', 'Madrid', 'London', 'Brussels'],
        'Madrid': ['Venice', 'Reykjavik', 'London', 'Santorini', 'Lisbon', 'Brussels'],
        'Santorini': ['Venice', 'London', 'Madrid'],
        'London': ['Brussels', 'Madrid', 'Santorini', 'Reykjavik', 'Lisbon', 'Venice']
    }
    
    # Fixed constraints
    fixed_constraints = [
        ('Brussels', 1, 2),  # Day 1-2 in Brussels
        ('Venice', 5, 7),    # Day 5-7 in Venice
        ('Madrid', 7, 11)    # Day 7-11 in Madrid
    ]
    
    # Generate all possible city orders (permutations)
    city_list = list(cities.keys())
    possible_orders = permutations(city_list)
    
    valid_itineraries = []
    
    for order in possible_orders:
        day_assignments = {}
        valid = True
        
        # Apply fixed constraints first
        for city, start, end in fixed_constraints:
            for day in range(start, end + 1):
                if day in day_assignments:
                    valid = False
                    break
                day_assignments[day] = city
            if not valid:
                break
        
        if not valid:
            continue
        
        # Now fill in the remaining cities
        prev_city = None
        current_day = 1
        
        for city in order:
            # Skip if this city is already assigned in fixed constraints
            if city in [c[0] for c in fixed_constraints]:
                continue
                
            required_days = cities[city]
            
            # Find earliest available contiguous block
            start_day = None
            for day in range(1, 18 - required_days + 1):
                # Check if days are available
                days_available = True
                for d in range(day, day + required_days):
                    if d in day_assignments:
                        days_available = False
                        break
                
                if not days_available:
                    continue
                
                # Check flight connection if needed
                if prev_city is not None:
                    # Need a flight day before
                    flight_day = day - 1
                    if flight_day < 1 or flight_day in day_assignments:
                        continue
                    if city not in flights[prev_city]:
                        valid = False
                        break
                
                start_day = day
                break
            
            if not start_day or not valid:
                valid = False
                break
            
            # Assign flight day if needed
            if prev_city is not None:
                flight_day = start_day - 1
                day_assignments[flight_day] = f"Flight from {prev_city} to {city}"
            
            # Assign stay days
            for day in range(start_day, start_day + required_days):
                day_assignments[day] = city
            
            prev_city = city
        
        # Verify we have exactly 17 days assigned (including flight days)
        if not valid or len(day_assignments) != 17:
            continue
        
        # Verify fixed constraints are met
        meets_constraints = True
        for city, start, end in fixed_constraints:
            for day in range(start, end + 1):
                if day not in day_assignments or day_assignments[day] != city:
                    meets_constraints = False
                    break
            if not meets_constraints:
                break
        
        if meets_constraints:
            # Format the itinerary
            formatted = []
            current_city = None
            start_day = 1
            
            for day in range(1, 18):
                location = day_assignments.get(day)
                
                if "Flight" in str(location):
                    # Add the flight day as a separate entry
                    formatted.append({
                        'day_range': f"Day {day}",
                        'place': location
                    })
                    continue
                
                if location != current_city:
                    if current_city is not None:
                        formatted.append({
                            'day_range': f"Day {start_day}-{day-1}",
                            'place': current_city
                        })
                    current_city = location
                    start_day = day
            
            # Add the last city
            if current_city is not None:
                formatted.append({
                    'day_range': f"Day {start_day}-17",
                    'place': current_city
                })
            
            valid_itineraries.append(formatted)
    
    if not valid_itineraries:
        return {"itinerary": []}
    
    # Select the first valid itinerary
    selected_itinerary = valid_itineraries[0]
    
    return {"itinerary": selected_itinerary}

if __name__ == "__main__":
    itinerary = find_itinerary()
    print(json.dumps(itinerary, indent=2))