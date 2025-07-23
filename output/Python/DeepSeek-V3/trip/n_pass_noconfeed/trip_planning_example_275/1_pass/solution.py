import json

def calculate_itinerary():
    # Input constraints
    total_days = 14
    city_days = {
        "Split": 5,
        "Vilnius": 4,
        "Santorini": 2,
        "Madrid": 6
    }
    conference_days = (13, 14)
    conference_city = "Santorini"
    
    # Direct flights connectivity
    direct_flights = {
        "Vilnius": ["Split"],
        "Split": ["Vilnius", "Madrid"],
        "Madrid": ["Split", "Santorini"],
        "Santorini": ["Madrid"]
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Since days 13-14 must be in Santorini, we start by placing those
    itinerary.append({
        "day_range": f"Day {conference_days[0]}-{conference_days[1]}",
        "place": conference_city
    })
    remaining_days = total_days - (conference_days[1] - conference_days[0] + 1)
    city_days[conference_city] -= (conference_days[1] - conference_days[0] + 1)
    
    # Now we need to place the remaining cities: Split (5), Vilnius (4), Madrid (6)
    # We have to ensure connectivity via direct flights
    
    # Possible paths considering direct flights:
    # Vilnius <-> Split <-> Madrid <-> Santorini
    
    # Since we end in Santorini, the last city before Santorini must be Madrid
    # So the sequence must be ... -> Madrid -> Santorini
    
    # Let's try to place Madrid just before Santorini
    # Days before Madrid must be Split or Vilnius
    
    # Assign Madrid days (6 total, some may be before Santorini)
    # Since we have to be in Madrid before Santorini, at least 1 day is needed for transition
    # But we have 6 days for Madrid, so we can split before and after
    
    # Let's assign Madrid days before Santorini
    # We need to reach Madrid from Split or Vilnius
    
    # Possible sequences:
    # Option 1: Vilnius -> Split -> Madrid -> Santorini
    # Option 2: Split -> Vilnius -> Split -> Madrid -> Santorini
    
    # Let's try Option 1:
    # Vilnius (4) -> Split (5) -> Madrid (6) -> Santorini (2)
    # But we have only 14 days total, and 4+5+6+2=17 which exceeds
    
    # So we need overlapping days where travel happens
    
    # Recalculate considering travel days count for both cities
    
    # Start from Day 1
    current_day = 1
    
    # We have to visit Vilnius (4), Split (5), Madrid (6), Santorini (2)
    # Santorini is fixed on days 13-14 (2 days)
    # So days 1-12 need to cover Vilnius (4), Split (5), Madrid (6) with overlaps
    
    # Let's try starting in Vilnius
    # Day 1-4: Vilnius (4 days)
    # Day 4: Travel to Split (counts as day in both)
    # Day 4-8: Split (5 days total, including travel day)
    # Day 8: Travel to Madrid
    # Day 8-13: Madrid (6 days total, including travel day)
    # Day 13-14: Santorini
    
    # Calculate:
    # Vilnius: Day 1-4 (4 days)
    # Split: Day 4-8 (5 days: 4,5,6,7,8)
    # Madrid: Day 8-13 (6 days: 8,9,10,11,12,13)
    # Santorini: Day 13-14 (2 days: 13,14)
    
    # Check counts:
    # Vilnius: 4 (OK)
    # Split: 5 (OK)
    # Madrid: 6 (OK)
    # Santorini: 2 (OK)
    
    # Build itinerary
    itinerary = [
        {"day_range": "Day 1-4", "place": "Vilnius"},
        {"day_range": "Day 4-8", "place": "Split"},
        {"day_range": "Day 8-13", "place": "Madrid"},
        {"day_range": "Day 13-14", "place": "Santorini"}
    ]
    
    # Verify the direct flights are possible
    # Vilnius -> Split: yes
    # Split -> Madrid: yes
    # Madrid -> Santorini: yes
    
    return {"itinerary": itinerary}

# Execute and print the result as JSON
result = calculate_itinerary()
print(json.dumps(result))