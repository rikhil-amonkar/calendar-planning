import json

def main():
    total_days = 18
    city_days = {
        'Split': 6,
        'Santorini': 7,
        'London': 7
    }
    conference_days = [12, 18]
    direct_flights = [('London', 'Santorini'), ('Split', 'London')]
    
    # Determine city order: must end in Santorini (due to day 18)
    # Santorini must be preceded by London (only direct flight to Santorini is from London)
    # Therefore, order must be: Split -> London -> Santorini
    
    # Calculate boundaries
    split_end = city_days['Split']  # Last day in Split (flight day to London)
    santorini_start = total_days - city_days['Santorini'] + 1  # First day in Santorini
    london_days_calculated = santorini_start - split_end + 1  # Days in London (inclusive range)
    
    # Validate constraints
    valid_itinerary = True
    if london_days_calculated != city_days['London']:
        valid_itinerary = False
    for day in conference_days:
        if day < santorini_start or day > total_days:
            valid_itinerary = False
    
    # Build itinerary if valid
    if valid_itinerary:
        itinerary = [
            {"day_range": f"Day 1-{split_end}", "place": "Split"},
            {"day_range": f"Day {split_end}-{santorini_start}", "place": "London"},
            {"day_range": f"Day {santorini_start}-{total_days}", "place": "Santorini"}
        ]
    else:
        itinerary = []
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()