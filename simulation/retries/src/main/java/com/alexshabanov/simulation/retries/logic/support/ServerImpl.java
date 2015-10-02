package com.alexshabanov.simulation.retries.logic.support;

import com.alexshabanov.simulation.retries.logic.Request;
import com.alexshabanov.simulation.retries.logic.Response;
import com.alexshabanov.simulation.retries.logic.Server;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author Alexander Shabanov
 */
public final class ServerImpl implements Server {
  private final int maxRequests;
  private final int ticksPerRequest;
  private final List<RequestData> waitRequestData;
  private final Map<Integer, Response> responseMap;

  public ServerImpl(int maxRequests, int ticksPerRequest) {
    this.maxRequests = maxRequests;
    this.ticksPerRequest = ticksPerRequest;
    this.waitRequestData = new ArrayList<>(maxRequests);
    this.responseMap = new HashMap<>(maxRequests * 2);
  }

  @Override public boolean enqueue(Request request) {
    if (waitRequestData.size() > maxRequests) {
      return false;
    }

    waitRequestData.add(new RequestData(request, ticksPerRequest));
    return true;
  }

  @Override public void tick() {
    final List<Integer> processedRequestIndexes = new ArrayList<>();
    for (int i = 0; i < waitRequestData.size(); ++i) {
      final RequestData requestData = waitRequestData.get(i);
      if ((--requestData.ticks) > 0) {
        continue;
      }

      processedRequestIndexes.add(i);
    }

    for (int i = processedRequestIndexes.size() - 1; i >= 0; --i) {
      final int index = processedRequestIndexes.get(i);
      final RequestData requestData = waitRequestData.remove(index);
      responseMap.put(requestData.request.taskId,
          new Response(requestData.request.taskId, "Done with task #" + index));
    }
  }

  @Override public Response poll(int taskId) {
    return responseMap.remove(taskId);
  }

  //
  // Private
  //

  private static final class RequestData {
    final Request request;
    int ticks;

    public RequestData(Request request, int ticks) {
      this.request = request;
      this.ticks = ticks;
    }
  }
}
