if __name__ == "__main__":
    result = build_itinerary()
    print(json.dumps(result, ensure_ascii=False))