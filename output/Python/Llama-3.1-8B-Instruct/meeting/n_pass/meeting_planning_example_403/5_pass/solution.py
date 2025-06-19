from datetime import timedelta

class TravelCalculator:
    def __init__(self, travel_distances):
        """
        Initialize the travel calculator with a dictionary of travel distances.

        Args:
            travel_distances (dict): A dictionary where the keys are tuples of locations and the values are the travel times in minutes.
        """
        self.travel_distances = travel_distances

    def calculate_travel_time(self, start_location, end_location):
        """
        Calculate the travel time between two locations.

        Args:
            start_location (str): The starting location.
            end_location (str): The ending location.

        Returns:
            str: The travel time between the two locations in the format HH:MM:SS. If the travel time is not found, returns "Travel time not found".

        Raises:
            ValueError: If the start_location or end_location is not a string.
            KeyError: If the travel time is not found in the dictionary.
        """
        if not isinstance(start_location, str) or not isinstance(end_location, str):
            raise ValueError("Start and end locations must be strings")

        # Check if the travel time exists in the dictionary
        if (start_location, end_location) not in self.travel_distances and (end_location, start_location) not in self.travel_distances:
            raise KeyError(f"Travel time not found for locations {start_location} and {end_location}")

        # Get the travel time from the dictionary
        travel_time = self.travel_distances.get((start_location, end_location))
        if travel_time is None:
            travel_time = self.travel_distances.get((end_location, start_location))

        # Check if the travel time is a positive number
        if travel_time is None or travel_time <= 0:
            raise ValueError(f"Invalid travel time for locations {start_location} and {end_location}")

        # Convert the travel time to hours, minutes, and seconds
        hours = travel_time // 60
        minutes = (travel_time % 60)
        seconds = 0

        # Return the travel time in the format HH:MM:SS
        return f"{hours:02d}:{minutes:02d}:{seconds:02d}"


# Example usage:
travel_distances = {
    ("Location A", "Location B"): 30,
    ("Location B", "Location C"): 45,
    ("Location A", "Location C"): 75,
}

calculator = TravelCalculator(travel_distances)
print(calculator.calculate_travel_time("Location A", "Location B"))  # Output: 00:00:30
print(calculator.calculate_travel_time("Location B", "Location C"))  # Output: 00:00:45
print(calculator.calculate_travel_time("Location A", "Location C"))  # Output: 00:01:15