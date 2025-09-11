import json

def main():
    total_days = 17
    days_in_vilnius = 7
    days_in_naples = 5
    days_in_vienna = 7
    naples_constraint_start = 1
    naples_constraint_end = 5
    
    # Calculate itinerary based on constraints
    # Must start in Naples to meet the day 1-5 constraint
    naples_start = naples_constraint_start
    naples_end = naples_start + days_in_naples - 1
    
    # Fly to Vienna on the same day as leaving Naples
    vienna_start = naples_end
    vienna_end = vienna_start + days_in_vienna - 1
    
    # Fly to Vilnius on the same day as leaving Vienna
    vilnius_start = vienna_end
    vilnius_end = vilnius_start + days_in_vilnius - 1
    
    # Verify total days match
    assert vilnius_end == total_days, "Itinerary does not match total days"
    
    itinerary = [
        {"day_range": f"Day {naples_start}-{naples_end}", "place": "Naples"},
        {"day_range": f"Day {vienna_start}-{vienna_end}", "place": "Vienna"},
        {"day_range": f"Day {vilnius_start}-{vilnius_end}", "place": "Vilnius"}
    ]
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()