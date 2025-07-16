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
        # Check if the order respects the fixed constraints
        fixed_cities = [constraint[0] for constraint in fixed_constraints]
        if not all(city in order for city in fixed_cities):
            continue
            
        # Initialize day assignments
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
        
        # Now fill in the remaining days
        current_day = 1
        prev_city = None
        
        for city in order:
            # Skip if this city is already assigned in fixed constraints
            if city in fixed_cities:
                continue
                
            # Find the earliest available slot for this city
            required_days = cities[city]
            start_day = None
            
            # Find a contiguous block of required_days that's not assigned
            for day in range(1, 18 - required_days + 1):
                if all(d not in day_assignments for d in range(day, day + required_days)):
                    # Check if we can fly from previous city
                    if prev_city is not None:
                        # Check if flight exists between prev_city and this city
                        if city not in flights[prev_city]:
                            valid = False
                            break
                        # Need a transition day (must be unassigned)
                        transition_day = day - 1
                        if transition_day < 1 or transition_day in day_assignments:
                            continue
                    start_day = day
                    break
            
            if not start_day or not valid:
                valid = False
                break
            
            # Assign the stay days
            for day in range(start_day, start_day + required_days):
                day_assignments[day] = city
            
            # Assign the transition day if needed
            if prev_city is not None:
                transition_day = start_day - 1
                day_assignments[transition_day] = f"Flight from {prev_city} to {city}"
            
            prev_city = city
        
        if not valid or len(day_assignments) != 17:
            continue
        
        # Verify all fixed constraints are still met
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
            start_day = None
            
            for day in range(1, 18):
                location = day_assignments.get(day)
                if "Flight" in str(location):
                    continue  # Skip flight days in final output
                
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
    print(json.dumps(itinerary))