import json
from itertools import permutations

def find_itinerary():
    # Define the constraints
    total_days = 12
    city_days = {
        'Prague': 2,
        'Berlin': 3,
        'Tallinn': 5,
        'Stockholm': 5
    }
    
    # Conference constraints
    conference_days = [6, 8]
    
    # Relative visit constraints
    relatives_start = 8
    relatives_end = 12
    
    # Direct flight connections
    connections = {
        'Berlin': ['Tallinn', 'Stockholm'],
        'Tallinn': ['Berlin', 'Prague', 'Stockholm'],
        'Prague': ['Tallinn', 'Stockholm'],
        'Stockholm': ['Tallinn', 'Prague', 'Berlin']
    }
    
    # Generate all possible city orders
    cities = list(city_days.keys())
    possible_orders = permutations(cities)
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Check if all cities are connected in the order
        valid_order = True
        for i in range(len(order) - 1):
            if order[i+1] not in connections[order[i]]:
                valid_order = False
                break
        if not valid_order:
            continue
        
        # Try to assign days to the order
        itinerary = []
        remaining_days = {city: city_days[city] for city in cities}
        current_city = None
        day = 1
        
        for city in order:
            if day > total_days:
                break
            
            # Determine the number of days to spend in this city
            days_in_city = remaining_days[city]
            
            # Check if we need to be in Berlin on conference days
            if city == 'Berlin':
                # Ensure conference days are covered
                for conf_day in conference_days:
                    if day <= conf_day < day + days_in_city:
                        pass  # OK
                    else:
                        # Need to adjust to cover conference days
                        if conf_day < day:
                            # Conference day already passed, invalid
                            days_in_city = 0
                            break
                        else:
                            # Move start day to cover conference
                            days_in_city = conf_day - day + 1
                            break
            
            # Check if we need to be in Tallinn for relatives
            if city == 'Tallinn':
                # Ensure relative visit days are covered
                if not (day <= relatives_start and day + days_in_city - 1 >= relatives_end - 1):
                    # Adjust to cover relative visit
                    if day > relatives_start:
                        # Too late, invalid
                        days_in_city = 0
                    else:
                        # Extend stay to cover relatives
                        days_in_city = (relatives_end - 1) - day + 1
            
            if days_in_city <= 0:
                continue
            
            # Check if we exceed total days
            if day + days_in_city - 1 > total_days:
                days_in_city = total_days - day + 1
            
            if days_in_city <= 0:
                continue
            
            # Assign the days
            end_day = day + days_in_city - 1
            itinerary.append({
                'day_range': f"Day {day}-{end_day}",
                'place': city
            })
            remaining_days[city] -= days_in_city
            day = end_day + 1
        
        # Check if all days are assigned and constraints are met
        if day > total_days and all(v == 0 for v in remaining_days.values()):
            # Verify conference days are in Berlin
            berlin_days = []
            for entry in itinerary:
                if entry['place'] == 'Berlin':
                    start = int(entry['day_range'].split('-')[0].split(' ')[1])
                    end = int(entry['day_range'].split('-')[1])
                    berlin_days.extend(range(start, end + 1))
            if all(conf_day in berlin_days for conf_day in conference_days):
                # Verify relative visit is in Tallinn
                tallinn_days = []
                for entry in itinerary:
                    if entry['place'] == 'Tallinn':
                        start = int(entry['day_range'].split('-')[0].split(' ')[1])
                        end = int(entry['day_range'].split('-')[1])
                        tallinn_days.extend(range(start, end + 1))
                if all(day in tallinn_days for day in range(relatives_start, relatives_end)):
                    valid_itineraries.append(itinerary)
    
    if not valid_itineraries:
        return {"itinerary": []}
    
    # Select the first valid itinerary (can be optimized further)
    selected_itinerary = valid_itineraries[0]
    
    return {"itinerary": selected_itinerary}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result))