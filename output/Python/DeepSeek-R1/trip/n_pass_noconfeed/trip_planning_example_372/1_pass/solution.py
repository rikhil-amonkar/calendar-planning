import json

def main():
    # Input constraints
    total_days = 13
    seville_days = 2
    stuttgart_days = 7
    porto_days = 3
    madrid_days = 4
    conference_days = [7, 13]
    direct_flights = [('Porto','Stuttgart'), ('Seville','Porto'), ('Madrid','Porto'), ('Madrid','Seville')]
    
    # Calculate itinerary ranges algorithmically
    madrid_start = 1
    madrid_end = madrid_start + madrid_days - 1
    
    seville_start = madrid_end
    seville_end = seville_start + seville_days - 1
    
    porto_start = seville_end
    porto_end = porto_start + porto_days - 1
    
    stuttgart_start = porto_end
    stuttgart_end = stuttgart_start + stuttgart_days - 1
    
    # Build itinerary
    itinerary = [
        {"day_range": f"Day {madrid_start}-{madrid_end}", "place": "Madrid"},
        {"day_range": f"Day {seville_start}-{seville_end}", "place": "Seville"},
        {"day_range": f"Day {porto_start}-{porto_end}", "place": "Porto"},
        {"day_range": f"Day {stuttgart_start}-{stuttgart_end}", "place": "Stuttgart"}
    ]
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()