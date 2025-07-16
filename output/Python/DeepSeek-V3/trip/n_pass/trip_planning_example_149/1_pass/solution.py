import json

def plan_trip():
    # Input parameters
    total_days = 10
    london_days = 3
    santorini_days = 6
    istanbul_days = 3
    conference_days = [5, 10]
    
    # Direct flights
    direct_flights = {
        'Istanbul': ['London'],
        'London': ['Istanbul', 'Santorini'],
        'Santorini': ['London']
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Since we must be in Santorini on days 5 and 10, and we want to spend 6 days there,
    # the Santorini visit must include days 5-10 (6 days)
    santorini_start = 5
    santorini_end = 10
    
    # Check if Santorini days match
    if (santorini_end - santorini_start + 1) != santorini_days:
        raise ValueError("Cannot satisfy Santorini days constraint")
    
    # Before Santorini, we must be in London or Istanbul (only London has direct flight to Santorini)
    # We have days 1-4 to spend in London or Istanbul
    # We need to spend 3 days in London and 3 in Istanbul in total
    
    # Days spent in London before Santorini
    london_before = min(london_days, 4)
    istanbul_before = 4 - london_before
    
    # Check if remaining days match
    remaining_london = london_days - london_before
    remaining_istanbul = istanbul_days - istanbul_before
    
    if remaining_london < 0 or remaining_istanbul < 0:
        raise ValueError("Cannot satisfy city days constraints")
    
    # After Santorini, there are no days left (since Santorini ends on day 10)
    if remaining_london + remaining_istanbul > 0:
        raise ValueError("Cannot satisfy city days constraints after Santorini")
    
    # Build itinerary
    current_day = 1
    
    # Istanbul before (if any)
    if istanbul_before > 0:
        itinerary.append({
            "day_range": f"Day {current_day}-{current_day + istanbul_before - 1}",
            "place": "Istanbul"
        })
        current_day += istanbul_before
    
    # London before
    if london_before > 0:
        itinerary.append({
            "day_range": f"Day {current_day}-{current_day + london_before - 1}",
            "place": "London"
        })
        current_day += london_before
    
    # Santorini
    itinerary.append({
        "day_range": f"Day {santorini_start}-{santorini_end}",
        "place": "Santorini"
    })
    
    # Verify total days
    total_itinerary_days = 0
    for entry in itinerary:
        start, end = map(int, entry['day_range'].split('Day ')[1].split('-'))
        total_itinerary_days += (end - start + 1)
    
    if total_itinerary_days != total_days:
        raise ValueError("Itinerary days do not match total days")
    
    return {"itinerary": itinerary}

# Execute and print the result as JSON
result = plan_trip()
print(json.dumps(result, indent=2))