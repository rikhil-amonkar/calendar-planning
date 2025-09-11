def main():
    total_days = 11
    seville_days = 6
    paris_days = 2
    krakow_days = 5
    krakow_workshop_start = 1
    krakow_workshop_end = 5
    
    # Calculate itinerary ranges
    krakow_start = 1
    krakow_end = krakow_start + krakow_days - 1
    
    paris_start = krakow_end
    paris_end = paris_start + paris_days - 1
    
    seville_start = paris_end
    seville_end = seville_start + seville_days - 1
    
    # Verify constraints
    assert krakow_end >= krakow_workshop_start and krakow_start <= krakow_workshop_end, "Krakow workshop constraint violated"
    assert seville_end == total_days, "Total days constraint violated"
    
    itinerary = [
        {"day_range": f"Day {krakow_start}-{krakow_end}", "place": "Krakow"},
        {"day_range": f"Day {paris_start}-{paris_end}", "place": "Paris"},
        {"day_range": f"Day {seville_start}-{seville_end}", "place": "Seville"}
    ]
    
    import json
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()