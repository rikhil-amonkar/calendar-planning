import json
from collections import defaultdict

class TripPlanner:
    def __init__(self, constraints):
        self.constraints = constraints
        self.cities = set()
        for city, duration in constraints.items():
            self.cities.add(city)
        self.flights = {
            'Reykjavik': ['Stuttgart'],
            'Stuttgart': ['Split', 'Vienna', 'Manchester'],
            'Split': ['Lyon', 'Manchester'],
            'Prague': ['Manchester', 'Reykjavik', 'Vienna'],
            'Vienna': ['Lyon', 'Manchester', 'Split'],
            'Manchester': ['Split', 'Prague'],
            'Lyon': ['Vienna'],
            'Edinburgh': ['Prague', 'Stuttgart'],
            'Stuttgart': ['Edinburgh']
        }

    def calculate_total_duration(self):
        total_duration = 0
        for duration in self.constraints.values():
            total_duration += duration
        return total_duration

    def adjust_durations(self, total_duration):
        sorted_durations = sorted(self.constraints.values(), reverse=True)
        adjusted_durations = {}
        remaining_days = total_duration
        for duration in sorted_durations:
            if remaining_days >= duration:
                adjusted_durations[list(self.constraints.keys())[list(self.constraints.values()).index(duration)]] = duration
                remaining_days -= duration
            else:
                adjusted_durations[list(self.constraints.keys())[list(self.constraints.values()).index(duration)]] = remaining_days
                break
        return adjusted_durations

    def compute_itinerary(self, adjusted_durations):
        itinerary = []
        day = 1
        current_city = list(self.cities)[0]
        current_duration = 0
        for city, duration in adjusted_durations.items():
            if city == current_city:
                current_duration += duration
            else:
                itinerary.append({"day_range": f"Day {day}-{day + duration - 1}", "place": current_city})
                day += duration
                current_duration = 0
                current_city = city
        # If there are remaining days, append the last city
        if current_duration > 0:
            itinerary.append({"day_range": f"Day {day}-{day + current_duration - 1}", "place": current_city})
        # If the total duration is less than 25, add the remaining days to the last city
        if day < 25:
            remaining_days = 25 - day
            itinerary[-1]["day_range"] = f"Day {itinerary[-1]['day_range'].split('-')[0]}-{itinerary[-1]['day_range'].split('-')[0]} + {remaining_days - 1}"
        return itinerary

    def plan_trip(self):
        total_duration = self.calculate_total_duration()
        adjusted_durations = self.adjust_durations(total_duration)
        # If the total duration is less than 25, adjust the durations to cover exactly 25 days
        if total_duration < 25:
            sorted_durations = sorted(self.constraints.values(), reverse=True)
            remaining_days = 25 - total_duration
            for duration in sorted_durations:
                if remaining_days >= duration:
                    adjusted_durations[list(self.constraints.keys())[list(self.constraints.values()).index(duration)]] += duration
                    remaining_days -= duration
                else:
                    adjusted_durations[list(self.constraints.keys())[list(self.constraints.values()).index(duration)]] += remaining_days
                    break
        itinerary = self.compute_itinerary(adjusted_durations)
        return {"itinerary": itinerary}

def load_constraints():
    constraints = {
        'Vienna': 4,
        'Lyon': 3,
        'Edinburgh': 4,
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Manchester': 2,
        'Split': 5,
        'Prague': 4
    }
    return constraints

def main():
    constraints = load_constraints()
    planner = TripPlanner(constraints)
    itinerary = planner.plan_trip()
    print(json.dumps(itinerary, indent=4))

if __name__ == "__main__":
    main()