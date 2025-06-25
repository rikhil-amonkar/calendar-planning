import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            "Oslo": 5,
            "Stuttgart": 5,
            "Reykjavik": 2,
            "Split": 3,
            "Geneva": 2,
            "Porto": 3,
            "Tallinn": 5,
            "Stockholm": 3
        }
        self.flights = {
            "Reykjavik": ["Stuttgart", "Stockholm", "Oslo"],
            "Stockholm": ["Oslo", "Tallinn", "Stuttgart", "Split", "Geneva"],
            "Oslo": ["Reykjavik", "Split", "Geneva", "Porto"],
            "Stuttgart": ["Reykjavik", "Porto", "Split"],
            "Split": ["Oslo", "Stuttgart", "Stockholm", "Geneva"],
            "Geneva": ["Stockholm", "Split", "Porto"],
            "Porto": ["Stuttgart", "Oslo", "Geneva"],
            "Tallinn": ["Reykjavik", "Oslo", "Stockholm"]
        }

    def calculate_itinerary(self):
        itinerary = []
        current_day = 1
        current_place = list(self.cities.keys())[0]
        visited = set()
        day_range = f"Day {current_day}-{current_day + self.cities[current_place] - 1}"
        itinerary.append({"day_range": day_range, "place": current_place})

        total_days = 0
        while total_days < 21:
            for _ in range(self.cities[current_place]):
                visited.add(current_place)
                current_day += 1
                total_days += 1

            next_places = self.flights[current_place]
            if current_place == "Reykjavik" and current_day >= 1 and current_day <= 2:
                next_places = ["Stuttgart"]
            elif current_place == "Reykjavik" and current_day >= 3 and current_day <= 4:
                next_places = ["Stockholm"]
            elif current_place == "Stockholm" and current_day >= 2 and current_day <= 4:
                next_places = [current_place]
            elif current_place == "Porto" and current_day >= 19 and current_day <= 21:
                next_places = [current_place]
            else:
                next_places = [p for p in next_places if p not in visited]

            if next_places:
                next_place = next_places[0]
                if next_place not in visited:
                    current_place = next_place
                    day_range = f"Day {current_day}-{current_day + self.cities[current_place] - 1}"
                    itinerary.append({"day_range": day_range, "place": current_place})
            else:
                break

        return {"itinerary": itinerary}

def main():
    trip_planner = TripPlanner()
    result = trip_planner.calculate_itinerary()
    print(json.dumps(result, indent=4))

if __name__ == "__main__":
    main()