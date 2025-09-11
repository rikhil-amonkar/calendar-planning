def main():
    total_days = 12
    vilnius_days = 4
    munich_days = 3
    mykonos_days = 7
    
    # Calculate total travel days needed
    total_requested_days = vilnius_days + munich_days + mykonos_days
    total_travel_days = total_requested_days - total_days  # 14 - 12 = 2
    
    # Since only direct flights are Vilnius-Munich and Munich-Mykonos,
    # we need one travel day between Vilnius-Munich and one between Munich-Mykonos
    travel_vm = 1
    travel_mk = 1
    
    # Calculate full days in each city (excluding travel days)
    full_vilnius = vilnius_days - travel_vm
    full_munich = munich_days - travel_vm - travel_mk
    full_mykonos = mykonos_days - travel_mk
    
    # Calculate day ranges for itinerary display
    # Assign travel days to arrival city for display purposes
    start_vilnius = 1
    end_vilnius = start_vilnius + full_vilnius - 1
    
    start_munich = end_vilnius + 1
    end_munich = start_munich + full_munich + travel_vm - 1
    
    start_mykonos = end_munich + 1
    end_mykonos = start_mykonos + full_mykonos + travel_mk - 1
    
    # Build itinerary segments
    itinerary = []
    if full_vilnius > 0:
        itinerary.append({
            "day_range": f"Day {start_vilnius}-{end_vilnius}",
            "place": "Vilnius"
        })
    
    munich_range = f"Day {start_munich}-{end_munich}"
    itinerary.append({
        "day_range": munich_range,
        "place": "Munich"
    })
    
    mykonos_range = f"Day {start_mykonos}-{end_mykonos}"
    itinerary.append({
        "day_range": mykonos_range,
        "place": "Mykonos"
    })
    
    # Output as JSON
    import json
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()