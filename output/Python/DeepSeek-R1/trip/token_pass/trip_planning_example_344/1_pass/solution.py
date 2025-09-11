import json

def main():
    # Given constraints
    total_days = 20
    required_days = {
        'Valencia': 6,
        'Athens': 6,
        'Naples': 5,
        'Zurich': 6
    }
    
    # Fixed events
    athens_event = (1, 6)
    naples_event = (16, 20)
    
    # Calculate flexible stays
    valencia_start = athens_event[1]  # Day 6
    valencia_end = valencia_start + required_days['Valencia'] - 1  # Day 11
    zurich_start = valencia_end  # Day 11
    zurich_end = zurich_start + required_days['Zurich'] - 1  # Day 16
    
    # Verify consistency with Naples event
    assert zurich_end == naples_event[0], "Itinerary calculation error"
    
    # Build itinerary
    itinerary = [
        {"day_range": f"Day {athens_event[0]}-{athens_event[1]}", "place": "Athens"},
        {"day_range": f"Day {valencia_start}-{valencia_end}", "place": "Valencia"},
        {"day_range": f"Day {zurich_start}-{zurich_end}", "place": "Zurich"},
        {"day_range": f"Day {naples_event[0]}-{naples_event[1]}", "place": "Naples"}
    ]
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()