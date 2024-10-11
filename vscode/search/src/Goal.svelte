<script lang="ts">
  export let searchResponse: SearchResponse;
  export let showLocation: (uri: string, range: Range) => void;

  function callback() {
    if (searchResponse.goalRange !== null) {
      showLocation(searchResponse.uri, searchResponse.goalRange);
    }
  }
</script>

{#if searchResponse.goalName === null}
  <h1><span class="mono">There is no goal.</span></h1>
{:else if searchResponse.goalRange === null}
  <h1><span class="mono">{searchResponse.goalName}</span></h1>
{:else}
  <h1><span class="mono goal-link" on:click={callback}
        >{searchResponse.goalName}</span>
  </h1>
{/if}

<style>
  .goal-link {
    cursor: pointer;
  }

  .goal-link:hover {
    text-decoration: underline;
  }
</style>
