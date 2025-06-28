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

    def compute_itinerary(self):
        itinerary = []
        day = 1
        current_city = list(self.cities)[0]
        current_duration = 0
        for city, duration in self.constraints.items():
            if city == current_city:
                current_duration += duration
            else:
                itinerary.append({"day_range": f"Day {day}-{day + duration - 1}", "place": current_city})
                day += duration
                current_duration = 0
                current_city = city
        itinerary.append({"day_range": f"Day {day}-{day + current_duration - 1}", "place": current_city})
        return itinerary

    def plan_trip(self):
        itinerary = self.compute_itinerary()
        for i, entry in enumerate(itinerary):
            if entry['place'] == 'Edinburgh' and day >= 5 and day <= 8:
                itinerary[i]['day_range'] = f"Day {day}-8"
            elif entry['place'] == 'Split' and day >= 19 and day <= 23:
                itinerary[i]['day_range'] = f"Day {day}-23"
            day = int(entry['day_range'].split('-')[1]) + 1
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