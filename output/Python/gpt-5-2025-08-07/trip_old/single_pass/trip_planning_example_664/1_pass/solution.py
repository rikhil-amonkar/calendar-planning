if __name__ == "__main__":
    result = {"itinerary": compute_itinerary()}
    print(json.dumps(result))