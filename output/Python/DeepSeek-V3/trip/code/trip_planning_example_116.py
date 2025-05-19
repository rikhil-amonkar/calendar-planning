import json

def plan_trip():
    total_days = 18
    days_in_split = 6
    days_in_santorini = 7
    days_in_london = 7
    conference_days = [12, 18]
    
    # Check if the total days add up correctly
    total_stay_days = days_in_split + days_in_santorini + days_in_london
    if total_stay_days != total_days:
        raise ValueError("Total stay days do not match the total trip days.")
    
    # Determine the sequence of cities based on direct flights
    # Possible sequences:
    # 1. Split -> London -> Santorini
    # 2. London -> Split -> Santorini
    # But Santorini must include day 12 and 18, so it must be the last city.
    
    # We'll choose Split -> London -> Santorini
    
    # Assign days to Split
    split_start = 1
    split_end = split_start + days_in_split - 1
    split_segment = {'day_range': f'Day {split_start}-{split_end}', 'place': 'Split'}
    
    # Flight from Split to London
    flight1_day = split_end + 1
    flight1_segment = {'flying': f'Day {flight1_day}-{flight1_day}', 'from': 'Split', 'to': 'London'}
    
    # Assign days to London
    london_start = flight1_day
    london_end = london_start + days_in_london - 1
    london_segment = {'day_range': f'Day {london_start}-{london_end}', 'place': 'London'}
    
    # Flight from London to Santorini
    flight2_day = london_end + 1
    flight2_segment = {'flying': f'Day {flight2_day}-{flight2_day}', 'from': 'London', 'to': 'Santorini'}
    
    # Assign days to Santorini
    santorini_start = flight2_day
    santorini_end = santorini_start + days_in_santorini - 1
    santorini_segment = {'day_range': f'Day {santorini_start}-{santorini_end}', 'place': 'Santorini'}
    
    # Verify conference days are in Santorini
    for day in conference_days:
        if not (santorini_start <= day <= santorini_end):
            raise ValueError("Conference days are not within the Santorini stay.")
    
    itinerary = [
        split_segment,
        flight1_segment,
        london_segment,
        flight2_segment,
        santorini_segment
    ]
    
    return itinerary

if __name__ == "__main__":
    itinerary = plan_trip()
    print(json.dumps(itinerary, indent=2))