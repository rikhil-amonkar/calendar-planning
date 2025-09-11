import json

def main():
    total_days = 10
    venice_days = 6
    mykonos_days = 2
    vienna_days = 4
    workshop_start = 5
    workshop_end = 10
    
    # Calculate transition days
    d1 = mykonos_days  # Last day in Mykonos
    d2 = d1 + vienna_days - 1  # Last day in Vienna
    
    # Verify Venice days
    venice_calculated = total_days - d2 + 1
    if venice_calculated != venice_days or d2 != workshop_start:
        print("No valid itinerary found with given constraints.")
        return
    
    # Build itinerary
    itinerary = [
        {"day_range": f"Day 1-{d1}", "place": "Mykonos"},
        {"day_range": f"Day {d1}-{d2}", "place": "Vienna"},
        {"day_range": f"Day {d2}-{total_days}", "place": "Venice"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()