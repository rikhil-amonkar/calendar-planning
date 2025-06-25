import json

def main():
    total_days = 7
    riga_days = 2
    amsterdam_days = 2
    mykonos_days = 5

    start_riga = 1
    end_riga = start_riga + riga_days - 1

    start_amsterdam = end_riga
    end_amsterdam = start_amsterdam + amsterdam_days - 1

    start_mykonos = end_amsterdam
    end_mykonos = start_mykonos + mykonos_days - 1

    itinerary = [
        {"day_range": f"Day {start_riga}-{end_riga}", "place": "Riga"},
        {"day_range": f"Day {start_amsterdam}-{end_amsterdam}", "place": "Amsterdam"},
        {"day_range": f"Day {start_mykonos}-{end_mykonos}", "place": "Mykonos"}
    ]

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()