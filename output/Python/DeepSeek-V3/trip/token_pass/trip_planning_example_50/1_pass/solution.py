import json

def plan_trip():
    total_days = 12
    vilnius_days_needed = 4
    munich_days_needed = 3
    mykonos_days_needed = 7
    
    # Direct flights: Munich-Mykonos, Vilnius-Munich
    # So only possible route: Vilnius -> Munich -> Mykonos
    # or reverse. We'll pick one.
    
    # Using earlier deduction:
    t_vm = 1  # travel Vilnius-Munich
    t_mk = 1  # travel Munich-Mykonos
    
    v_excl = vilnius_days_needed - t_vm
    m_excl = munich_days_needed - t_vm - t_mk
    k_excl = mykonos_days_needed - t_mk
    
    # Build itinerary
    itinerary = []
    day_counter = 1
    
    # Vilnius exclusive days
    if v_excl > 0:
        itinerary.append({
            "day_range": f"Day {day_counter}-{day_counter + v_excl - 1}",
            "place": "Vilnius"
        })
        day_counter += v_excl
    
    # Travel Vilnius -> Munich
    itinerary.append({
        "day_range": f"Day {day_counter}",
        "place": "Vilnius -> Munich (travel day)"
    })
    # This day counts for both Vilnius and Munich
    day_counter += 1
    
    # Munich exclusive days
    if m_excl > 0:
        itinerary.append({
            "day_range": f"Day {day_counter}-{day_counter + m_excl - 1}",
            "place": "Munich"
        })
        day_counter += m_excl
    
    # Travel Munich -> Mykonos
    itinerary.append({
        "day_range": f"Day {day_counter}",
        "place": "Munich -> Mykonos (travel day)"
    })
    day_counter += 1
    
    # Mykonos exclusive days
    if k_excl > 0:
        itinerary.append({
            "day_range": f"Day {day_counter}-{day_counter + k_excl - 1}",
            "place": "Mykonos"
        })
        day_counter += k_excl
    
    # Verify total days
    if day_counter - 1 != total_days:
        raise ValueError("Itinerary day count mismatch")
    
    # Return as JSON
    result = {"itinerary": itinerary}
    return json.dumps(result, indent=2)

if __name__ == "__main__":
    print(plan_trip())