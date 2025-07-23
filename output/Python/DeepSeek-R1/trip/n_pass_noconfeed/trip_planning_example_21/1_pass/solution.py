import json

def main():
    total_days = 10
    venice_days = 6
    mykonos_days = 2
    vienna_days = 4
    workshop_start = 5
    workshop_end = 10

    start_mykonos = 1
    end_mykonos = mykonos_days

    start_vienna = end_mykonos
    end_vienna = start_vienna + vienna_days - 1

    start_venice = end_vienna
    end_venice = start_venice + venice_days - 1

    itinerary = [
        {"day_range": f"Day {start_mykonos}-{end_mykonos}", "place": "Mykonos"},
        {"day_range": f"Day {start_vienna}-{end_vienna}", "place": "Vienna"},
        {"day_range": f"Day {start_venice}-{end_venice}", "place": "Venice"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()