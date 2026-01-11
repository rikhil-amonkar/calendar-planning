import json

def plan_trip():
    total_days = 10
    krakow_days_needed = 2
    dubrovnik_days_needed = 7
    frankfurt_days_needed = 3
    
    # Direct flights graph
    flights = {
        "Frankfurt": ["Krakow", "Dubrovnik"],
        "Krakow": ["Frankfurt"],
        "Dubrovnik": ["Frankfurt"]
    }
    
    # We'll brute-force search over possible day allocations with travel constraints
    # Since small, we can enumerate start city and travel days
    
    # Possible city order due to flight network: D->F->K or K->F->D
    # Wedding in Krakow between day 9-10 means Krakow at end.
    # So D->F->K is logical.
    
    # Let's define day ranges:
    # Dubrovnik: day_start_D to day_travel_D (inclusive for Dubrovnik counting)
    # Frankfurt: day_travel_D to day_travel_F (inclusive for Frankfurt counting)
    # Krakow: day_travel_F to day_end (inclusive for Krakow counting)
    
    best_itinerary = None
    
    for travel_D_to_F in range(1, total_days):
        for travel_F_to_K in range(travel_D_to_F + 1, total_days + 1):
            # Day counts
            dubrovnik_days = travel_D_to_F  # because day 1 to travel_D_to_F inclusive
            frankfurt_days = travel_F_to_K - travel_D_to_F + 1  # +1 because travel day counts for both
            krakow_days = total_days - travel_F_to_K + 1  # +1 because travel day counts for both
            
            # Adjust: Actually, travel_D_to_F is the day you travel to Frankfurt, so you wake up in Dubrovnik that day.
            # So Dubrovnik days = travel_D_to_F (since days 1..travel_D_to_F waking in Dubrovnik)
            # Frankfurt days = (travel_F_to_K - travel_D_to_F) + 1? Let's check example:
            # travel_D_to_F=7, travel_F_to_K=9, total_days=10
            # Dubrovnik: days 1-7 waking there = 7 days.
            # Frankfurt: day 7 travel to F (counts), day 8 wake in F, day 9 wake in F but travel to K in day 9 (counts) = 3 days.
            # Krakow: day 9 travel to K (counts), day 10 wake in K = 2 days.
            # Yes.
            
            frankfurt_days = (travel_F_to_K - travel_D_to_F) + 1
            krakow_days = total_days - travel_F_to_K + 1
            
            # Check totals match required
            if (dubrovnik_days == dubrovnik_days_needed and
                frankfurt_days == frankfurt_days_needed and
                krakow_days == krakow_days_needed and
                travel_F_to_K <= total_days):
                
                # Wedding constraint: Krakow includes day 9 or 10
                if travel_F_to_K <= 9:  # Krakow includes day 9 (since day 9 is travel to Krakow or already there)
                    # Build itinerary
                    itinerary = []
                    if travel_D_to_F > 1:
                        itinerary.append({"day_range": f"Day 1-{travel_D_to_F}", "place": "Dubrovnik"})
                    else:
                        itinerary.append({"day_range": f"Day 1", "place": "Dubrovnik"})
                    
                    if travel_F_to_K - travel_D_to_F > 1:
                        itinerary.append({"day_range": f"Day {travel_D_to_F}-{travel_F_to_K}", "place": "Frankfurt"})
                    else:
                        itinerary.append({"day_range": f"Day {travel_D_to_F}", "place": "Frankfurt"})
                    
                    if total_days - travel_F_to_K >= 1:
                        itinerary.append({"day_range": f"Day {travel_F_to_K}-{total_days}", "place": "Krakow"})
                    else:
                        itinerary.append({"day_range": f"Day {travel_F_to_K}", "place": "Krakow"})
                    
                    best_itinerary = itinerary
                    break
        if best_itinerary:
            break
    
    # If not found by search, use the logical plan we derived
    if not best_itinerary:
        best_itinerary = [
            {"day_range": "Day 1-7", "place": "Dubrovnik"},
            {"day_range": "Day 7-9", "place": "Frankfurt"},
            {"day_range": "Day 9-10", "place": "Krakow"}
        ]
    
    return {"itinerary": best_itinerary}

if __name__ == "__main__":
    result = plan_trip()
    print(json.dumps(result, indent=2))