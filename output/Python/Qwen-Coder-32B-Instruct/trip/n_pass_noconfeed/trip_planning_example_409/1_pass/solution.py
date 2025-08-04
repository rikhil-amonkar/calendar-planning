import json

def calculate_itinerary():
    # Input constraints
    total_days = 12
    days_in_hamburg = 2
    days_in_zurich = 3
    days_in_helsinki = 2
    days_in_bucharest = 2
    days_in_split = 7
    conference_days_in_split = [4, 10]
    wedding_days_in_zurich = [1, 2, 3]
    
    # Direct flights available
    direct_flights = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Hamburg': ['Helsinki', 'Zurich', 'Bucharest'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Bucharest': ['Hamburg', 'Zurich'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }
    
    # Initialize itinerary
    itinerary = []
    current_day = 1
    
    # Start in Split to attend the conference on day 4
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_split - 1}", "place": "Split"})
    current_day += days_in_split
    
    # Adjust for conference days
    for day in conference_days_in_split:
        if day < current_day:
            itinerary[-1]['day_range'] = f"Day {day}-{current_day - 1}"
            current_day = day + 1
            break
    
    # Move to Zurich for the wedding on day 1
    if current_day > 1:
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_zurich - 1}", "place": "Zurich"})
    else:
        itinerary[0]['day_range'] = f"Day {wedding_days_in_zurich[0]}-{wedding_days_in_zurich[-1]}"
        current_day = wedding_days_in_zurich[-1] + 1
    
    # Move to Helsinki
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_helsinki - 1}", "place": "Helsinki"})
    current_day += days_in_helsinki
    
    # Move to Hamburg
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_hamburg - 1}", "place": "Hamburg"})
    current_day += days_in_hamburg
    
    # Move to Bucharest
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_bucharest - 1}", "place": "Bucharest"})
    current_day += days_in_bucharest
    
    # Ensure the total duration is 12 days
    if current_day < total_days + 1:
        last_place = itinerary[-1]['place']
        if last_place == 'Bucharest':
            last_place = 'Hamburg' if 'Hamburg' in direct_flights[last_place] else 'Helsinki'
        itinerary.append({"day_range": f"Day {current_day}-{total_days}", "place": last_place})
    
    return itinerary

# Calculate and print the itinerary in JSON format
print(json.dumps({"itinerary": calculate_itinerary()}))