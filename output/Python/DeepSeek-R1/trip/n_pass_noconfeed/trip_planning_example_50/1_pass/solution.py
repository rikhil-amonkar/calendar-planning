import json

def main():
    total_days = 12
    days_in_vilnius = 4
    days_in_munich = 3
    days_in_mykonos = 7

    start_vilnius = 1
    end_vilnius = days_in_vilnius

    start_munich = end_vilnius
    end_munich = start_munich + days_in_munich - 1

    start_mykonos = end_munich
    end_mykonos = total_days

    itinerary = [
        {"day_range": f"Day {start_vilnius}-{end_vilnius}", "place": "Vilnius"},
        {"day_range": f"Day {start_munich}-{end_munich}", "place": "Munich"},
        {"day_range": f"Day {start_mykonos}-{end_mykonos}", "place": "Mykonos"}
    ]

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()