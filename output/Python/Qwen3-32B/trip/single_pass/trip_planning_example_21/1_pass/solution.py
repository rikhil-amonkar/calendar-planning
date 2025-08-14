import json

def main():
    cities = {
        "Mykonos": 2,
        "Vienna": 4,
        "Venice": 6
    }

    possible_sequences = [
        ["Mykonos", "Vienna", "Venice"],
        ["Vienna", "Venice", "Vienna", "Mykonos"]
    ]

    for sequence in possible_sequences:
        stay_days = []
        for i, city in enumerate(sequence):
            if i == 0:
                required = cities[city]
                stay_days.append(required - 1)
            elif i == len(sequence) - 1:
                required = cities[city]
                stay_days.append(required - 1)
            else:
                required = cities[city]
                stay_days.append(required - 2)
        if all(d >= 0 for d in stay_days):
            total_days = sum(stay_days) + (len(sequence) - 1)
            if total_days == 10:
                itinerary = []
                start_day = 1
                for i, city in enumerate(sequence):
                    if i == 0:
                        days_in_city = stay_days[i] + 1
                    elif i == len(sequence) - 1:
                        days_in_city = stay_days[i] + 1
                    else:
                        days_in_city = stay_days[i] + 2
                    end_day = start_day + days_in_city - 1
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
                    start_day = end_day
                print(json.dumps({"itinerary": itinerary}))
                return

if __name__ == "__main__":
    main()