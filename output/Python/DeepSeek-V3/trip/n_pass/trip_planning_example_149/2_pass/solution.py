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
    # the only possible Santorini visit is days 5-10 (6 days)
    santorini_start = 5
    santorini_end = 10
    
    # Check if Santorini days match
    if (santorini_end - santorini_start + 1) != santorini_days:
        raise ValueError("Cannot satisfy Santorini days constraint")
    
    # Calculate days before and after Santorini
    days_before = santorini_start - 1
    days_after = total_days - santorini_end
    
    # We need to allocate 3 days to London and 3 to Istanbul
    # Possible allocations:
    # Option 1: All London before Santorini (3 days), then Istanbul after (3 days)
    # But we only have 4 days before and 0 after - doesn't work
    # Option 2: Split between before and after
    
    # Since we have 4 days before and 0 after, we can't satisfy both city requirements
    # Therefore, we need to adjust Santorini days to allow time after
    
    # Alternative solution: Reduce Santorini days to allow time for other cities
    # But we must include both conference days (5 and 10)
    # Minimum Santorini visit that includes both days is 6 days (5-10)
    # So we can't reduce it
    
    # Therefore, the constraints cannot be satisfied as given
    raise ValueError("Cannot satisfy all constraints with given parameters - need more days or adjust city days")

# Execute and print the result as JSON
try:
    result = plan_trip()
    print(json.dumps(result, indent=2))
except ValueError as e:
    print(json.dumps({"error": str(e)}, indent=2))