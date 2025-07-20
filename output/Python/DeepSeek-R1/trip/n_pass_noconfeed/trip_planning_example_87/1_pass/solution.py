import json

def main():
    total_days = 7
    riga_days = 2
    amsterdam_days = 2
    mykonos_days = 5

    # Calculate itinerary segments
    riga_start = 1
    riga_end = riga_start + riga_days - 1

    amsterdam_start = riga_end
    amsterdam_end = amsterdam_start + amsterdam_days - 1

    mykonos_start = amsterdam_end
    mykonos_end = total_days

    itinerary = [
        {"day_range": f"Day {riga_start}-{riga_end}", "place": "Riga"},
        {"day_range": f"Day {amsterdam_start}-{amsterdam_end}", "place": "Amsterdam"},
        {"day_range": f"Day {mykonos_start}-{mykonos_end}", "place": "Mykonos"}
    ]

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()