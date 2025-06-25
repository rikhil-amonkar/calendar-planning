import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            "Reykjavik": 4,
            "Riga": 2,
            "Oslo": 3,
            "Lyon": 5,
            "Dubrovnik": 2,
            "Madrid": 2,
            "Warsaw": 4,
            "London": 3
        }
        self.flights = {
            "Warsaw": ["Reykjavik"],
            "Oslo": ["Madrid", "Warsaw", "Reykjavik", "Riga", "Lyon"],
            "Riga": ["Oslo", "Warsaw"],
            "Lyon": ["Oslo", "London"],
            "Dubrovnik": ["Oslo", "Madrid"],
            "Madrid": ["Warsaw", "Lyon", "London"],
            "Warsaw": ["Reykjavik", "Riga", "Oslo", "Madrid", "London"],
            "London": ["Lyon", "Madrid", "Warsaw", "Reykjavik", "Oslo"]
        }
        self.meetings = {
            "Riga": [(4, 5)],
            "Dubrovnik": [(7, 8)]
        }
        self.total_days = 18

    def calculate_itinerary(self):
        # Sort cities by number of days
        sorted_cities = sorted(self.cities.items(), key=lambda x: x[1], reverse=True)

        # Initialize itinerary and current day
        itinerary = []
        current_day = 1

        # Iterate over sorted cities
        for city, days in sorted_cities:
            # Add city to itinerary
            itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": city})

            # Update current day
            current_day += days

            # Check for meetings
            if city in self.meetings:
                for start, end in self.meetings[city]:
                    itinerary.append({"day_range": f"Day {start}-{end}", "place": city})

            # Check for flights
            if city in self.flights:
                for flight in self.flights[city]:
                    # Find next city with a flight to this city
                    for next_city, next_flights in self.flights.items():
                        if flight in next_flights:
                            # Calculate transition day
                            transition_day = current_day + self.cities[city] - 1
                            # Add transition to itinerary
                            itinerary.append({"day_range": f"Day {transition_day}-{transition_day}", "place": flight})

                            # Update current day
                            current_day = transition_day + 1

            # Check if total days exceeded
            if current_day > self.total_days:
                # Remove last city from itinerary
                itinerary.pop()
                # Break the loop
                break

        # Check if itinerary covers exactly 18 days
        if current_day < self.total_days:
            # Remove last city from itinerary
            itinerary.pop()

        return itinerary

    def output_json(self, itinerary):
        return json.dumps({"itinerary": itinerary}, indent=4)

def main():
    planner = TripPlanner()
    itinerary = planner.calculate_itinerary()
    print(planner.output_json(itinerary))

if __name__ == "__main__":
    main()