import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Reykjavik': {'Munich': 1, 'Oslo': 1, 'Frankfurt': 1, 'Stockholm': 1},
            'Munich': {'Reykjavik': 1, 'Frankfurt': 1, 'Oslo': 1, 'Bucharest': 1, 'Stockholm': 1},
            'Frankfurt': {'Munich': 1, 'Oslo': 1, 'Bucharest': 1, 'Barcelona': 1, 'Stockholm': 1},
            'Oslo': {'Reykjavik': 1, 'Munich': 1, 'Frankfurt': 1, 'Bucharest': 1, 'Split': 1},
            'Bucharest': {'Munich': 1, 'Frankfurt': 1, 'Oslo': 1, 'Barcelona': 1},
            'Split': {'Oslo': 1, 'Barcelona': 1, 'Stockholm': 1, 'Frankfurt': 1, 'Munich': 1},
            'Barcelona': {'Bucharest': 1, 'Frankfurt': 1, 'Stockholm': 1, 'Reykjavik': 1, 'Oslo': 1, 'Munich': 1},
            'Stockholm': {'Reykjavik': 1, 'Munich': 1, 'Frankfurt': 1, 'Barcelona': 1, 'Split': 1, 'Oslo': 1}
        }
        self.constraints = {
            'Reykjavik': 5,
            'Oslo': {'start': 2, 'end': 3},
            'Frankfurt': {'start': 17, 'end': 20},
            'Barcelona': 3,
            'Bucharest': 2,
            'Split': 3,
            'Munich': 4,
            'Stockholm': 4
        }

    def compute_itinerary(self):
        days = 20
        places = list(self.cities.keys())
        itinerary = defaultdict(list)
        current_place = places[0]
        current_days = 0
        visited = set()

        for place in places:
            if place in self.constraints:
                duration = self.constraints[place]
                if isinstance(duration, dict):
                    start_day = duration['start']
                    end_day = duration['end']
                else:
                    start_day = current_days
                    end_day = current_days + duration - 1
                itinerary['day_range'].append(f"Day {start_day}-{end_day}")
                itinerary['place'].append(place)
                visited.add(place)
                current_days = end_day

        remaining_days = days - current_days
        for place in places:
            if place not in visited:
                for neighbor in self.cities[place]:
                    if neighbor not in visited:
                        transition_day = current_days + self.cities[place][neighbor]
                        if transition_day <= days:
                            itinerary['day_range'].append(f"Day {current_days+1}-{transition_day}")
                            itinerary['place'].append(neighbor)
                            visited.add(neighbor)
                            current_days = transition_day
                            remaining_days -= 1
                            if remaining_days == 0:
                                break

        # Fill the remaining days with the first unvisited place
        first_unvisited_place = next((place for place in places if place not in visited), None)
        if first_unvisited_place:
            transition_day = current_days + self.cities[places[0]][first_unvisited_place]
            itinerary['day_range'].append(f"Day {current_days+1}-{transition_day}")
            itinerary['place'].append(first_unvisited_place)
            visited.add(first_unvisited_place)
            current_days = transition_day

        return {'itinerary': [{'day_range': day_range, 'place': place} for day_range, place in zip(itinerary['day_range'], itinerary['place'])]}

    def output_json(self, itinerary):
        return json.dumps(itinerary, indent=4)

def main():
    planner = TripPlanner()
    itinerary = planner.compute_itinerary()
    print(planner.output_json(itinerary))

if __name__ == "__main__":
    main()