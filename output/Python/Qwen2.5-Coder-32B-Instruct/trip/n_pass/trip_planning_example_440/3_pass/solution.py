import json

def calculate_itinerary():
    # Input constraints
    total_days = 12
    split_days = 2
    helsinki_days = 2
    reykjavik_days = 3
    reykjavik_wedding_days = range(10, 13)
    vilnius_days = 3
    vilnius_relative_days = range(7, 10)
    geneva_days = 2  # Adjusted to fit the total of 12 days
    
    # Direct flight connections
    flights = {
        'Split': ['Helsinki', 'Geneva'],
        'Helsinki': ['Split', 'Geneva', 'Reykjavik', 'Vilnius'],
        'Geneva': ['Split', 'Helsinki'],
        'Reykjavik': ['Helsinki'],
        'Vilnius': ['Helsinki']
    }
    
    # Initialize itinerary
    itinerary = []
    current_day = 1
    current_city = None
    
    # Place constraints into a list of tuples (city, days, priority, specific_days)
    constraints = [
        ('Split', split_days, 1, None),
        ('Helsinki', helsinki_days, 1, None),
        ('Reykjavik', reykjavik_days, 2, reykjavik_wedding_days),
        ('Vilnius', vilnius_days, 2, vilnius_relative_days),
        ('Geneva', geneva_days, 3, None)
    ]
    
    # Sort constraints by priority
    constraints.sort(key=lambda x: x[2])
    
    # Function to check if a city can be visited on a given day
    def can_visit(city, day):
        if current_city is None:
            return True
        if city in flights[current_city]:
            return True
        return False
    
    # Function to find the next possible city to visit
    def find_next_city(day):
        for city, days, priority, specific_days in constraints:
            if specific_days:
                if day in specific_days:
                    return city
            else:
                return city
        return None
    
    # Build the itinerary
    while current_day <= total_days:
        next_city = find_next_city(current_day)
        if next_city and can_visit(next_city, current_day):
            city_days = next((days for city, days, _, _ in constraints if city == next_city), 0)
            # Ensure we do not exceed total_days
            end_day = min(current_day + city_days - 1, total_days)
            itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": next_city})
            current_day = end_day + 1
            current_city = next_city
            # Remove the city from constraints once it's been added to the itinerary
            constraints = [c for c in constraints if c[0] != next_city]
        else:
            current_day += 1
    
    # If the itinerary does not cover all days, add a placeholder or adjust the last entry
    if current_day < total_days + 1:
        remaining_days = total_days - (current_day - 1)
        if itinerary:
            last_entry = itinerary[-1]
            last_city = last_entry['place']
            last_end_day = int(last_entry['day_range'].split('-')[1].split(' ')[1])
            new_end_day = last_end_day + remaining_days
            itinerary[-1]['day_range'] = f"Day {last_end_day - last_days + 1}-{new_end_day}"
        else:
            itinerary.append({"day_range": f"Day {current_day}-{total_days}", "place": "Placeholder"})
    
    return itinerary

# Calculate and print the itinerary as JSON
itinerary_result = calculate_itinerary()
print(json.dumps({"itinerary": itinerary_result}))