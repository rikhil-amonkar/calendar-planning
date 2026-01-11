import json

def plan_trip():
    total_days = 15
    stuttgart_days_needed = 6
    seville_days_needed = 7
    manchester_days_needed = 4
    
    # Direct flights: Manchester-Seville, Stuttgart-Manchester
    # So only possible route visiting all three: Stuttgart -> Manchester -> Seville
    # Let d1 = last day in Stuttgart (flight to Manchester on d1)
    # Let d2 = last day in Manchester (flight to Seville on d2)
    # Then:
    # Stuttgart days = d1
    # Manchester days = d2 - d1 + 1
    # Seville days = total_days - d2 + 1
    
    found = False
    itinerary = []
    
    for d1 in range(1, total_days + 1):
        for d2 in range(d1, total_days + 1):
            stuttgart = d1
            manchester = d2 - d1 + 1
            seville = total_days - d2 + 1
            if (stuttgart == stuttgart_days_needed and
                manchester == manchester_days_needed and
                seville == seville_days_needed):
                # Build itinerary
                itinerary.append({"day_range": f"Day 1-{d1}", "place": "Stuttgart"})
                itinerary.append({"day_range": f"Day {d1}-{d2}", "place": "Manchester"})
                itinerary.append({"day_range": f"Day {d2}-{total_days}", "place": "Seville"})
                found = True
                break
        if found:
            break
    
    if not found:
        # Fallback: try other permutations of city order if needed
        # But given constraints, one should exist.
        itinerary = [{"day_range": "Day 1-15", "place": "No valid itinerary found"}]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    plan_trip()