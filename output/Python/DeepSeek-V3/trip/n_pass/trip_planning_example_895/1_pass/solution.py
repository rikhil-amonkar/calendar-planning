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
        itinerary = []
        current_day = 1
        valid = True
        
        # Check fixed constraints first
        for city, start, end in fixed_constraints:
            if city not in order:
                valid = False
                break
        
        if not valid:
            continue
        
        # Build itinerary based on order
        temp_itinerary = []
        prev_city = None
        
        for city in order:
            if prev_city is not None:
                # Check if flight exists
                if city not in flights[prev_city]:
                    valid = False
                    break
                # Transition day (counts for both cities)
                transition_day = current_day
                temp_itinerary.append((transition_day, transition_day, city))
                current_day += 1
            
            # Add stay days
            required_days = cities[city]
            start_day = current_day
            end_day = current_day + required_days - 1
            temp_itinerary.append((start_day, end_day, city))
            current_day = end_day + 1
            prev_city = city
        
        if not valid or current_day - 1 > 17:
            continue
        
        # Check fixed constraints
        temp_days = {}
        for (start, end, city) in temp_itinerary:
            for day in range(start, end + 1):
                temp_days[day] = city
        
        # Verify fixed constraints
        meets_constraints = True
        for city, start, end in fixed_constraints:
            for day in range(start, end + 1):
                if day not in temp_days or temp_days[day] != city:
                    meets_constraints = False
                    break
            if not meets_constraints:
                break
        
        if meets_constraints:
            # Format itinerary
            formatted = []
            current_entry = None
            for (start, end, city) in temp_itinerary:
                if current_entry and current_entry['place'] == city:
                    current_entry['day_range'] = f"Day {current_entry['day_range'].split('-')[0]}-{end}"
                else:
                    if current_entry:
                        formatted.append(current_entry)
                    current_entry = {
                        'day_range': f"Day {start}-{end}",
                        'place': city
                    }
            if current_entry:
                formatted.append(current_entry)
            
            valid_itineraries.append(formatted)
    
    if not valid_itineraries:
        return {"itinerary": []}
    
    # Select the first valid itinerary (can be optimized further)
    selected_itinerary = valid_itineraries[0]
    
    return {"itinerary": selected_itinerary}

if __name__ == "__main__":
    itinerary = find_itinerary()
    print(json.dumps(itinerary))