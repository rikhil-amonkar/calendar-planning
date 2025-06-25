import json

def main():
    total_days = 17
    city_days = {
        'Vilnius': 7,
        'Naples': 5,
        'Vienna': 7
    }
    naples_constraint = (1, 5)
    
    # Calculate Naples stay (must be within days 1-5, 5 consecutive days only possible as days 1-5)
    naples_start = naples_constraint[0]
    naples_end = naples_start + city_days['Naples'] - 1
    
    # Determine next city after Naples: must be Vienna due to direct flight constraint
    vienna_start = naples_end  # Travel day: day 5 counts for both Naples and Vienna
    vienna_end = vienna_start + city_days['Vienna'] - 1
    
    # After Vienna, go to Vilnius (direct flight available)
    vilnius_start = vienna_end  # Travel day: day 11 counts for both Vienna and Vilnius
    vilnius_end = vilnius_start + city_days['Vilnius'] - 1
    
    # Verify total days
    total_accounted = city_days['Naples'] + city_days['Vienna'] + city_days['Vilnius'] - 2  # Subtract two travel days
    assert total_accounted == total_days, "Total days do not match"
    assert vilnius_end == total_days, "Itinerary exceeds total days"
    
    itinerary = [
        {"day_range": f"Day {naples_start}-{naples_end}", "place": "Naples"},
        {"day_range": f"Day {vienna_start}-{vienna_end}", "place": "Vienna"},
        {"day_range": f"Day {vilnius_start}-{vilnius_end}", "place": "Vilnius"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()